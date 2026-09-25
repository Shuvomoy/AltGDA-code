
module C123LMI
include("c123_lmi_feasibility.jl")
end

using Dates
using Printf

const H_VALUES = collect(2:5)
const EIGENVALUE_ETA = 0.1
const START_ETA = 0.04
const PROBES = [0.1, 0.2, 0.4, 0.8, 1.2]
const ETA_CAP = 1.2
const ETA_TOLERANCE = 1e-3
const LOWER_ETA_FLOOR = 1e-3
const LOWER_PROBES = [0.02, 0.01, 0.005, LOWER_ETA_FLOOR]
const LOWER_ETA_TOLERANCE = 1e-4
const HEATMAP_ETAS = [
    0.001,
    0.002,
    0.005,
    0.01,
    0.02,
    0.04,
    0.06,
    0.08,
    0.1,
    0.125,
    0.15,
    0.175,
    0.2,
    0.225,
    0.25,
    0.3,
    0.35,
    0.4,
    0.45,
    0.5,
    0.55,
    0.6,
]
const RESIDUAL_TOL = 1e-6
const EIG_TOL = -1e-7
const LAMBDA_TOL = -1e-8
const DIAGNOSTIC_SCORE_FLOOR = 1e-16
const STRICT_OPTIMAL = true

function csv_escape(value)
    value === nothing && return ""
    value === missing && return ""
    text = string(value)
    if occursin(",", text) || occursin("\"", text) || occursin("\n", text)
        return "\"" * replace(text, "\"" => "\"\"") * "\""
    end
    return text
end

function write_csv(path::String, rows, columns)
    open(path, "w") do io
        println(io, join(columns, ","))
        for row in rows
            println(io, join([csv_escape(get(row, col, "")) for col in columns], ","))
        end
    end
end

function strict_primal_point(result)
    result === nothing && return false
    return get(result, "termination_status", "") == "OPTIMAL" &&
        get(result, "primal_status", "") == "FEASIBLE_POINT"
end

function strict_certified(result)
    result === nothing && return false
    return strict_primal_point(result) && get(result, "passed", false)
end

function diagnostic_values(result)
    max_residual = get(result, "max_abs_lmi_residual", nothing)
    min_eig = get(result, "min_psd_eigenvalue", nothing)
    min_lambda = get(result, "min_lambda", nothing)
    available = max_residual !== nothing && min_eig !== nothing && min_lambda !== nothing
    return available, max_residual, min_eig, min_lambda
end

function diagnostic_score(result)
    available, max_residual, min_eig, min_lambda = diagnostic_values(result)
    if !available
        return false, 0.0, 0.0, 0.0, 0.0, 0.0
    end
    residual_ratio = max_residual / RESIDUAL_TOL
    psd_violation_ratio = max(0.0, (EIG_TOL - min_eig) / abs(EIG_TOL))
    lambda_violation_ratio = max(0.0, (LAMBDA_TOL - min_lambda) / abs(LAMBDA_TOL))
    score = max(residual_ratio, psd_violation_ratio, lambda_violation_ratio)
    log_score = log10(max(score, DIAGNOSTIC_SCORE_FLOOR))
    return true, residual_ratio, psd_violation_ratio, lambda_violation_ratio, score, log_score
end

function independent_diagnostics_pass(result)
    available, max_residual, min_eig, min_lambda = diagnostic_values(result)
    return available &&
        max_residual <= RESIDUAL_TOL &&
        min_eig >= EIG_TOL &&
        min_lambda >= LAMBDA_TOL
end

function solve_strict_threshold_point(h::Int, eta::Float64, phase::String; silent::Bool)
    return C123LMI.solve_threshold_point(
        h,
        eta,
        phase;
        silent,
        residual_tol = RESIDUAL_TOL,
        eig_tol = EIG_TOL,
        lambda_tol = LAMBDA_TOL,
        solver = C123LMI.DEFAULT_SOLVER,
        strict_optimal = STRICT_OPTIMAL,
    )
end

function find_solve_at_eta(solves, eta)
    eta === nothing && return nothing
    for result in reverse(solves)
        if haskey(result, "eta") && result["eta"] == eta
            return result
        end
    end
    return nothing
end

function lower_endpoint_search_for_h(h::Int; silent::Bool)
    solves = Any[]
    start = solve_strict_threshold_point(h, START_ETA, "lower_start"; silent)
    push!(solves, start)
    if !strict_certified(start)
        return Dict{String, Any}(
            "h" => h,
            "lower_threshold_status" => "start_not_certified_feasible",
            "certified_lower_endpoint" => nothing,
            "first_noncertified_below_eta" => START_ETA,
            "lower_interval_width" => nothing,
            "left_censored_at_floor" => false,
            "certified_lower_result" => nothing,
            "first_noncertified_below_result" => start,
            "solves" => solves,
        )
    end

    certified_high = start
    for eta in LOWER_PROBES
        eta >= START_ETA && continue
        result = solve_strict_threshold_point(h, eta, "lower_probe"; silent)
        push!(solves, result)
        if strict_certified(result)
            certified_high = result
            continue
        end

        noncertified_low = result
        while certified_high["eta"] - noncertified_low["eta"] > LOWER_ETA_TOLERANCE
            midpoint = 0.5 * (certified_high["eta"] + noncertified_low["eta"])
            midpoint_result = solve_strict_threshold_point(h, midpoint, "lower_bisection"; silent)
            push!(solves, midpoint_result)
            if strict_certified(midpoint_result)
                certified_high = midpoint_result
            else
                noncertified_low = midpoint_result
            end
        end

        return Dict{String, Any}(
            "h" => h,
            "lower_threshold_status" => "bracketed",
            "certified_lower_endpoint" => certified_high["eta"],
            "first_noncertified_below_eta" => noncertified_low["eta"],
            "lower_interval_width" => certified_high["eta"] - noncertified_low["eta"],
            "left_censored_at_floor" => false,
            "certified_lower_result" => certified_high,
            "first_noncertified_below_result" => noncertified_low,
            "solves" => solves,
        )
    end

    return Dict{String, Any}(
        "h" => h,
        "lower_threshold_status" => "left_censored_at_floor",
        "certified_lower_endpoint" => LOWER_ETA_FLOOR,
        "first_noncertified_below_eta" => nothing,
        "lower_interval_width" => nothing,
        "left_censored_at_floor" => true,
        "certified_lower_result" => certified_high,
        "first_noncertified_below_result" => nothing,
        "solves" => solves,
    )
end

function endpoint_fields(prefix::String, result)
    fields = Dict{String, Any}()
    fields["$(prefix)_termination_status"] = result === nothing ? nothing : get(result, "termination_status", nothing)
    fields["$(prefix)_primal_status"] = result === nothing ? nothing : get(result, "primal_status", nothing)
    fields["$(prefix)_max_abs_lmi_residual"] =
        result === nothing ? nothing : get(result, "max_abs_lmi_residual", nothing)
    fields["$(prefix)_min_psd_eigenvalue"] =
        result === nothing ? nothing : get(result, "min_psd_eigenvalue", nothing)
    fields["$(prefix)_min_lambda"] = result === nothing ? nothing : get(result, "min_lambda", nothing)
    fields["$(prefix)_strict_mosek_certified"] = result === nothing ? false : strict_certified(result)
    return fields
end

function eta_range_row(generated_at::String, lower_summary, upper_summary)
    eta_min = lower_summary["certified_lower_endpoint"]
    eta_max = upper_summary["certified_lower_bound"]
    upper_result = find_solve_at_eta(upper_summary["solves"], eta_max)
    lower_result = lower_summary["certified_lower_result"]
    display_floor_result = find_solve_at_eta(lower_summary["solves"], LOWER_ETA_FLOOR)
    display_eta_min = LOWER_ETA_FLOOR
    range_certified = eta_min !== nothing &&
        eta_max !== nothing &&
        eta_min <= eta_max &&
        strict_certified(lower_result) &&
        strict_certified(upper_result)
    row = Dict{String, Any}(
        "generated_at" => generated_at,
        "formulation_id" => 1,
        "formulation" => "one_step_c123_lmi",
        "h" => upper_summary["h"],
        "eta_min" => eta_min,
        "eta_max" => eta_max,
        "eta_midpoint" => range_certified ? 0.5 * (eta_min + eta_max) : nothing,
        "eta_radius" => range_certified ? 0.5 * (eta_max - eta_min) : nothing,
        "display_eta_min" => display_eta_min,
        "display_eta_max" => eta_max,
        "display_eta_midpoint" => eta_max === nothing ? nothing : 0.5 * (display_eta_min + eta_max),
        "display_eta_radius" => eta_max === nothing ? nothing : 0.5 * (eta_max - display_eta_min),
        "display_floor_diagnostics_pass" => independent_diagnostics_pass(display_floor_result),
        "left_censored_at_floor" => lower_summary["left_censored_at_floor"],
        "first_noncertified_below_eta" => lower_summary["first_noncertified_below_eta"],
        "first_noncertified_above_eta" => upper_summary["first_infeasible_or_ambiguous"],
        "lower_threshold_status" => lower_summary["lower_threshold_status"],
        "upper_threshold_status" => upper_summary["threshold_status"],
        "lower_interval_width" => lower_summary["lower_interval_width"],
        "upper_interval_width" => upper_summary["final_interval_width"],
        "range_certified" => range_certified,
        "strict_optimal" => STRICT_OPTIMAL,
        "eta_lower_floor" => LOWER_ETA_FLOOR,
        "lower_eta_tolerance" => LOWER_ETA_TOLERANCE,
        "upper_eta_tolerance" => ETA_TOLERANCE,
        "residual_tol" => RESIDUAL_TOL,
        "eig_tol" => EIG_TOL,
        "lambda_tol" => LAMBDA_TOL,
        "included_psd_matrices" => C123LMI.INCLUDED_PSD_MATRICES,
    )
    merge!(row, endpoint_fields("display_floor", display_floor_result))
    merge!(row, endpoint_fields("lower_endpoint", lower_result))
    merge!(row, endpoint_fields("upper_endpoint", upper_result))
    return row
end

function eta_diagnostic_row(generated_at::String, result)
    return Dict{String, Any}(
        "generated_at" => generated_at,
        "formulation_id" => 1,
        "formulation" => "one_step_c123_lmi",
        "h" => result["h"],
        "eta" => result["eta"],
        "mosek_termination_status" => result["termination_status"],
        "mosek_primal_status" => result["primal_status"],
        "mosek_max_abs_lmi_residual" => get(result, "max_abs_lmi_residual", missing),
        "mosek_min_psd_eigenvalue" => get(result, "min_psd_eigenvalue", missing),
        "mosek_min_lambda" => get(result, "min_lambda", missing),
        "lambda_min_Qx" => get(result, "lambda_min_Qx", missing),
        "lambda_min_Qy" => get(result, "lambda_min_Qy", missing),
        "sigma_plus_Qx" => get(result, "sigma_plus_Qx", missing),
        "sigma_plus_Qy" => get(result, "sigma_plus_Qy", missing),
        "mosek_certified" => get(result, "passed", false),
        "strict_optimal" => STRICT_OPTIMAL,
        "residual_tol" => RESIDUAL_TOL,
        "eig_tol" => EIG_TOL,
        "lambda_tol" => LAMBDA_TOL,
        "included_psd_matrices" => C123LMI.INCLUDED_PSD_MATRICES,
    )
end

function heatmap_row(generated_at::String, result, eta_grid_index::Int)
    score_available, residual_ratio, psd_violation_ratio, lambda_violation_ratio, score, log_score =
        diagnostic_score(result)
    point_ok = strict_primal_point(result) && score_available
    certified = point_ok && get(result, "passed", false)
    return Dict{String, Any}(
        "generated_at" => generated_at,
        "formulation_id" => 1,
        "formulation" => "one_step_c123_lmi",
        "h" => result["h"],
        "eta" => result["eta"],
        "eta_grid_index" => eta_grid_index,
        "mosek_termination_status" => get(result, "termination_status", nothing),
        "mosek_primal_status" => get(result, "primal_status", nothing),
        "strict_mosek_primal_point" => point_ok,
        "strict_mosek_primal_point_id" => point_ok ? 1 : 0,
        "mosek_max_abs_lmi_residual" => get(result, "max_abs_lmi_residual", nothing),
        "mosek_min_psd_eigenvalue" => get(result, "min_psd_eigenvalue", nothing),
        "mosek_min_lambda" => get(result, "min_lambda", nothing),
        "diagnostic_score_available" => score_available,
        "residual_ratio" => score_available ? residual_ratio : nothing,
        "psd_violation_ratio" => score_available ? psd_violation_ratio : nothing,
        "lambda_violation_ratio" => score_available ? lambda_violation_ratio : nothing,
        "diagnostic_score" => score_available ? score : nothing,
        "log10_diagnostic_score" => score_available ? log_score : 0.0,
        "strict_mosek_certified" => certified,
        "strict_mosek_certified_id" => certified ? 1 : 0,
        "threshold_classification" => get(result, "threshold_classification", nothing),
        "strict_optimal" => STRICT_OPTIMAL,
        "residual_tol" => RESIDUAL_TOL,
        "eig_tol" => EIG_TOL,
        "lambda_tol" => LAMBDA_TOL,
        "included_psd_matrices" => C123LMI.INCLUDED_PSD_MATRICES,
    )
end

function parse_output_dir(args)
    idx = findfirst(==("--output-dir"), args)
    idx === nothing && return joinpath(@__DIR__, "Data")
    idx < length(args) || error("--output-dir requires a path")
    return args[idx + 1]
end

function usage()
    println("""
    Usage:
      julia Code/export_c123_lmi_figure_data.jl [--output-dir PATH] [--verbose]

    Writes C1-C2-C3 Section 5 MOSEK diagnostic CSV files:
      c123_lmi_optimal_eta_ranges.csv
      c123_lmi_optimal_eta_heatmap.csv
      c123_lmi_eta0p1_diagnostics.csv
    """)
end

function main(args)
    if "--help" in args || "-h" in args
        usage()
        return 0
    end

    output_dir = parse_output_dir(args)
    mkpath(output_dir)
    silent = !("--verbose" in args)
    generated_at = string(now())

    eta_range_rows = Any[]
    eta_rows = Any[]
    heatmap_rows = Any[]
    all_ranges_certified = true
    all_eta_certified = true

    for h in H_VALUES
        upper_summary = C123LMI.threshold_search_for_h(
            h;
            start_eta = START_ETA,
            probes = PROBES,
            cap = ETA_CAP,
            eta_tolerance = ETA_TOLERANCE,
            residual_tol = RESIDUAL_TOL,
            eig_tol = EIG_TOL,
            lambda_tol = LAMBDA_TOL,
            silent,
            solver = C123LMI.DEFAULT_SOLVER,
            strict_optimal = STRICT_OPTIMAL,
        )
        lower_summary = lower_endpoint_search_for_h(h; silent)
        range_row = eta_range_row(generated_at, lower_summary, upper_summary)
        push!(eta_range_rows, range_row)
        all_ranges_certified &= range_row["range_certified"]

        result = solve_strict_threshold_point(h, EIGENVALUE_ETA, "eta0p1"; silent)
        push!(eta_rows, eta_diagnostic_row(generated_at, result))
        all_eta_certified &= get(result, "passed", false)

        for (eta_grid_index, eta) in enumerate(HEATMAP_ETAS)
            heatmap_result = solve_strict_threshold_point(h, eta, "heatmap"; silent)
            push!(heatmap_rows, heatmap_row(generated_at, heatmap_result, eta_grid_index))
        end
    end

    eta_path = joinpath(output_dir, "c123_lmi_optimal_eta_ranges.csv")
    heatmap_path = joinpath(output_dir, "c123_lmi_optimal_eta_heatmap.csv")
    diagnostics_path = joinpath(output_dir, "c123_lmi_eta0p1_diagnostics.csv")

    write_csv(
        eta_path,
        eta_range_rows,
        [
            "generated_at",
            "formulation_id",
            "formulation",
            "h",
            "eta_min",
            "eta_max",
            "eta_midpoint",
            "eta_radius",
            "display_eta_min",
            "display_eta_max",
            "display_eta_midpoint",
            "display_eta_radius",
            "display_floor_diagnostics_pass",
            "left_censored_at_floor",
            "first_noncertified_below_eta",
            "first_noncertified_above_eta",
            "lower_threshold_status",
            "upper_threshold_status",
            "lower_interval_width",
            "upper_interval_width",
            "range_certified",
            "strict_optimal",
            "eta_lower_floor",
            "lower_eta_tolerance",
            "upper_eta_tolerance",
            "residual_tol",
            "eig_tol",
            "lambda_tol",
            "included_psd_matrices",
            "display_floor_termination_status",
            "display_floor_primal_status",
            "display_floor_max_abs_lmi_residual",
            "display_floor_min_psd_eigenvalue",
            "display_floor_min_lambda",
            "display_floor_strict_mosek_certified",
            "lower_endpoint_termination_status",
            "lower_endpoint_primal_status",
            "lower_endpoint_max_abs_lmi_residual",
            "lower_endpoint_min_psd_eigenvalue",
            "lower_endpoint_min_lambda",
            "lower_endpoint_strict_mosek_certified",
            "upper_endpoint_termination_status",
            "upper_endpoint_primal_status",
            "upper_endpoint_max_abs_lmi_residual",
            "upper_endpoint_min_psd_eigenvalue",
            "upper_endpoint_min_lambda",
            "upper_endpoint_strict_mosek_certified",
        ],
    )
    write_csv(
        heatmap_path,
        heatmap_rows,
        [
            "generated_at",
            "formulation_id",
            "formulation",
            "h",
            "eta",
            "eta_grid_index",
            "mosek_termination_status",
            "mosek_primal_status",
            "strict_mosek_primal_point",
            "strict_mosek_primal_point_id",
            "mosek_max_abs_lmi_residual",
            "mosek_min_psd_eigenvalue",
            "mosek_min_lambda",
            "diagnostic_score_available",
            "residual_ratio",
            "psd_violation_ratio",
            "lambda_violation_ratio",
            "diagnostic_score",
            "log10_diagnostic_score",
            "strict_mosek_certified",
            "strict_mosek_certified_id",
            "threshold_classification",
            "strict_optimal",
            "residual_tol",
            "eig_tol",
            "lambda_tol",
            "included_psd_matrices",
        ],
    )
    write_csv(
        diagnostics_path,
        eta_rows,
        [
            "generated_at",
            "formulation_id",
            "formulation",
            "h",
            "eta",
            "mosek_termination_status",
            "mosek_primal_status",
            "mosek_max_abs_lmi_residual",
            "mosek_min_psd_eigenvalue",
            "mosek_min_lambda",
            "lambda_min_Qx",
            "lambda_min_Qy",
            "sigma_plus_Qx",
            "sigma_plus_Qy",
            "mosek_certified",
            "strict_optimal",
            "residual_tol",
            "eig_tol",
            "lambda_tol",
            "included_psd_matrices",
        ],
    )

    println("Wrote $(length(eta_range_rows)) C1-C2-C3 strict eta-range row(s) to $eta_path")
    println("Wrote $(length(heatmap_rows)) C1-C2-C3 strict heatmap diagnostic row(s) to $heatmap_path")
    println("Wrote $(length(eta_rows)) C1-C2-C3 eta=0.1 diagnostic row(s) to $diagnostics_path")
    for row in eta_range_rows
        @printf(
            "h=%d eta_min=%s eta_max=%s lower_status=%s upper_status=%s certified=%s\n",
            row["h"],
            string(row["eta_min"]),
            string(row["eta_max"]),
            row["lower_threshold_status"],
            row["upper_threshold_status"],
            string(row["range_certified"]),
        )
    end
    return all_ranges_certified && all_eta_certified ? 0 : 1
end

if abspath(PROGRAM_FILE) == @__FILE__
    exit(main(ARGS))
end
