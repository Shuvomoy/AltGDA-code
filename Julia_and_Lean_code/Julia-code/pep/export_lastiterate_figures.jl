
using Printf
using Statistics

if !isdefined(@__MODULE__, :read_simple_csv)
    include(joinpath(@__DIR__, "csv.jl"))
end

const S04_HORIZONS = collect(5:30)
const S04_FULL_WINDOW = (name = "full_5_30", T_min = 5, T_max = 30)
const S04_TAIL_WINDOW = (name = "tail_15_30", T_min = 15, T_max = 30)
const S04_FIT_WINDOWS = (S04_FULL_WINDOW, S04_TAIL_WINDOW)
const S04_PFEAS_TOLERANCE = 1e-4
const S04_DFEAS_TOLERANCE = 1e-4
const S04_FLAT_TOLERANCE = 1e-3
const S04_ROUNDED_ETA_TOLERANCE = 5.000001e-4
const S04_NEAR_MINUS_ONE_TOLERANCE = 0.25

const S04_SUMMARY_HEADER = [
    "N",
    "performance_measure",
    "solver",
    "classification",
    "selected_eta_c",
    "selected_eta",
    "selected_objective",
    "all_optimal",
    "num_solves",
    "total_solve_seconds",
    "final_eta_c_lo",
    "final_eta_c_hi",
    "boundary_widenings",
    "eta_grid_spacing",
    "validation_reference_eta",
    "validation_reference_objective",
    "validation_objective_error",
    "validation_eta_match",
    "validation_pass",
    "decision",
    "decision_reason",
]

const S04_CURVE_HEADER = [
    "N",
    "performance_measure",
    "search_phase",
    "search_round",
    "eta_c",
    "eta",
    "objective",
    "termination_status",
    "primal_status",
    "dual_status",
    "solver",
    "pfeas_tolerance",
    "dfeas_tolerance",
    "solve_seconds",
    "selected",
]

const S04_PEP_EXPORT_HEADER = [
    "T",
    "optimized_eta",
    "optimized_duality_gap",
]

const S04_GAP_FIGURE_HEADER = [
    "T",
    "ergodic_duality_gap",
    "last_iterate_duality_gap",
    "guide_T_minus_1",
    "guide_T_minus_half",
]

const S04_ETA_FIGURE_HEADER = [
    "T",
    "ergodic_optimized_eta",
    "last_iterate_selected_eta",
    "absolute_eta_difference",
]

const S04_FIT_SUMMARY_HEADER = [
    "series",
    "window",
    "T_min",
    "T_max",
    "n",
    "log_base",
    "intercept",
    "slope",
    "prefactor",
    "sse_log",
    "sst_log",
    "r_squared",
    "rmse_log",
    "slope_standard_error",
    "max_relative_fit_error",
]

const S04_FIT_POINTS_HEADER = [
    "series",
    "window",
    "T",
    "duality_gap",
    "log_T",
    "log_gap",
    "fitted_log_gap",
    "fitted_gap",
    "log_residual",
]

struct S04NarrativeContingency <: Exception
    message::String
end

Base.showerror(io::IO, error::S04NarrativeContingency) = print(io, error.message)

function _s04_header(path::AbstractString)::Vector{String}
    isfile(path) || throw(ArgumentError("CSV file does not exist: $(path)"))
    records = _parse_csv_records(read(path, String))
    isempty(records) && throw(ArgumentError("CSV file is empty: $(path)"))
    header = copy(first(records))
    if !isempty(header) && !isempty(header[1]) && first(header[1]) == '\ufeff'
        header[1] = chop(header[1]; head = 1, tail = 0)
    end
    return header
end

function _s04_require_header(path::AbstractString, expected::Vector{String})
    observed = _s04_header(path)
    observed == expected || throw(ArgumentError(
        "unexpected CSV schema in $(path): $(join(observed, ','))",
    ))
    return nothing
end

function _s04_parse_float(row, name::String, context::AbstractString)::Float64
    value = try
        parse(Float64, row[name])
    catch
        throw(ArgumentError("$(context) has an invalid $(name) value"))
    end
    isfinite(value) || throw(ArgumentError("$(context) has a nonfinite $(name) value"))
    return value
end

function _s04_parse_int(row, name::String, context::AbstractString)::Int
    return try
        parse(Int, row[name])
    catch
        throw(ArgumentError("$(context) has an invalid $(name) value"))
    end
end

_s04_key(value::Real) = @sprintf("%.14g", Float64(value))

function _s04_matches(left::Real, right::Real; rtol = 2e-12, atol = 0.0)
    return isapprox(Float64(left), Float64(right); rtol = rtol, atol = atol)
end

function _s04_validate_summary_rows(rows)
    length(rows) == length(S04_HORIZONS) || throw(ArgumentError(
        "sweep summary must contain exactly 26 rows",
    ))
    observed = [_s04_parse_int(row, "N", "sweep summary") for row in rows]
    observed == S04_HORIZONS || throw(ArgumentError(
        "sweep summary horizons must be the ordered set N=5:30",
    ))
    for (N, row) in zip(S04_HORIZONS, rows)
        context = "sweep summary N=$(N)"
        row["performance_measure"] == "lst" || throw(ArgumentError("$(context) is not last-iterate evidence"))
        row["solver"] == "mosek" || throw(ArgumentError("$(context) is not authoritative MOSEK evidence"))
        row["classification"] == "flat" || throw(ArgumentError("$(context) is not classified flat"))
        row["all_optimal"] == "true" || throw(ArgumentError("$(context) contains a non-strict result"))
        row["decision"] == "COMPLETE" || throw(ArgumentError("$(context) is not COMPLETE"))
        _s04_parse_int(row, "num_solves", context) == 26 || throw(ArgumentError("$(context) must record 26 solves"))
        _s04_parse_int(row, "boundary_widenings", context) == 0 || throw(ArgumentError("$(context) unexpectedly widened its bracket"))
        selected_eta_c = _s04_parse_float(row, "selected_eta_c", context)
        selected_eta = _s04_parse_float(row, "selected_eta", context)
        selected_objective = _s04_parse_float(row, "selected_objective", context)
        selected_eta_c > 0 && selected_eta > 0 && selected_objective > 0 || throw(ArgumentError(
            "$(context) has a nonpositive selected scalar",
        ))
        _s04_matches(selected_eta, inv(selected_eta_c)) || throw(ArgumentError(
            "$(context) has inconsistent selected eta and eta_c",
        ))
    end
    return nothing
end

function _s04_validate_curve_rows(rows, N::Integer, summary_row)
    context = "sweep curve N=$(N)"
    length(rows) == 26 || throw(ArgumentError("$(context) must contain exactly 26 rows"))
    eta_c_keys = String[]
    for row in rows
        _s04_parse_int(row, "N", context) == N || throw(ArgumentError("$(context) contains another horizon"))
        row["performance_measure"] == "lst" || throw(ArgumentError("$(context) contains another measure"))
        row["solver"] == "mosek" || throw(ArgumentError("$(context) contains a non-MOSEK row"))
        row["termination_status"] == "OPTIMAL" || throw(ArgumentError("$(context) contains a non-OPTIMAL row"))
        row["primal_status"] == "FEASIBLE_POINT" || throw(ArgumentError("$(context) contains a non-feasible primal row"))
        row["dual_status"] == "FEASIBLE_POINT" || throw(ArgumentError("$(context) contains a non-feasible dual row"))
        pfeas = _s04_parse_float(row, "pfeas_tolerance", context)
        dfeas = _s04_parse_float(row, "dfeas_tolerance", context)
        _s04_matches(pfeas, S04_PFEAS_TOLERANCE) || throw(ArgumentError("$(context) has a noncanonical primal tolerance"))
        _s04_matches(dfeas, S04_DFEAS_TOLERANCE) || throw(ArgumentError("$(context) has a noncanonical dual tolerance"))
        eta_c = _s04_parse_float(row, "eta_c", context)
        eta = _s04_parse_float(row, "eta", context)
        objective = _s04_parse_float(row, "objective", context)
        solve_seconds = _s04_parse_float(row, "solve_seconds", context)
        eta_c > 0 && eta > 0 && objective > 0 && solve_seconds >= 0 || throw(ArgumentError(
            "$(context) contains a nonpositive scalar or negative runtime",
        ))
        _s04_matches(eta, inv(eta_c)) || throw(ArgumentError("$(context) has inconsistent eta and eta_c"))
        push!(eta_c_keys, _s04_key(eta_c))
        row["selected"] in ("true", "false") || throw(ArgumentError("$(context) has an invalid selected flag"))
    end
    length(unique(eta_c_keys)) == 26 || throw(ArgumentError("$(context) contains a duplicate eta_c"))
    coarse_rows = filter(row -> row["search_phase"] == "coarse", rows)
    length(coarse_rows) == 25 || throw(ArgumentError(
        "$(context) must contain 25 coarse rows",
    ))
    all(row["search_round"] == "0" for row in coarse_rows) || throw(ArgumentError(
        "$(context) coarse rows must have search round zero",
    ))
    expected_grid = exp.(range(log(0.5), log(64.0); length = 25))
    expected_grid[1] = 0.5
    expected_grid[end] = 64.0
    observed_grid = sort([_s04_parse_float(row, "eta_c", context) for row in coarse_rows])
    all(_s04_matches(observed, expected; rtol = 5e-12) for (observed, expected) in zip(observed_grid, expected_grid)) || throw(ArgumentError(
        "$(context) does not contain the exact 25-point log grid on [0.5,64]",
    ))
    coarse_objectives = [_s04_parse_float(row, "objective", context) for row in coarse_rows]
    maximum(coarse_objectives) - minimum(coarse_objectives) < S04_FLAT_TOLERANCE || throw(ArgumentError(
        "$(context) does not satisfy the predeclared flatness criterion",
    ))
    selected_rows = filter(row -> row["selected"] == "true", rows)
    length(selected_rows) == 1 || throw(ArgumentError("$(context) must contain exactly one selected row"))
    selected = only(selected_rows)
    selected["search_phase"] == "canonical_flat" || throw(ArgumentError(
        "$(context) selected row is not the canonical flat-curve evaluation",
    ))
    selected["search_round"] == "0" || throw(ArgumentError(
        "$(context) canonical flat-curve row must have search round zero",
    ))
    count(row -> row["search_phase"] == "canonical_flat", rows) == 1 || throw(ArgumentError(
        "$(context) must contain exactly one canonical-flat row",
    ))
    for (curve_name, summary_name) in (
        ("eta_c", "selected_eta_c"),
        ("eta", "selected_eta"),
        ("objective", "selected_objective"),
    )
        curve_value = _s04_parse_float(selected, curve_name, context)
        summary_value = _s04_parse_float(summary_row, summary_name, "sweep summary N=$(N)")
        _s04_matches(curve_value, summary_value) || throw(ArgumentError(
            "$(context) selected $(curve_name) disagrees with its summary",
        ))
    end
    return selected
end

function _s04_validate_jld_curve_rows(rows, N::Integer)
    context = "aggregate JLD curve N=$(N)"
    length(rows) == 26 || throw(ArgumentError("$(context) must contain exactly 26 rows"))
    keys = String[]
    for row in rows
        Int(row["N"]) == N || throw(ArgumentError("$(context) contains another horizon"))
        row["performance_measure"] == "lst" || throw(ArgumentError("$(context) contains another measure"))
        row["solver"] == "mosek" || throw(ArgumentError("$(context) contains a non-MOSEK row"))
        row["termination_status"] == "OPTIMAL" || throw(ArgumentError("$(context) contains a non-OPTIMAL row"))
        row["primal_status"] == "FEASIBLE_POINT" || throw(ArgumentError("$(context) contains a non-feasible primal row"))
        row["dual_status"] == "FEASIBLE_POINT" || throw(ArgumentError("$(context) contains a non-feasible dual row"))
        _s04_matches(row["pfeas_tolerance"], S04_PFEAS_TOLERANCE) || throw(ArgumentError("$(context) has a noncanonical primal tolerance"))
        _s04_matches(row["dfeas_tolerance"], S04_DFEAS_TOLERANCE) || throw(ArgumentError("$(context) has a noncanonical dual tolerance"))
        eta_c = Float64(row["eta_c"])
        eta = Float64(row["eta"])
        objective = Float64(row["objective"])
        isfinite(eta_c) && eta_c > 0 && isfinite(eta) && eta > 0 &&
            isfinite(objective) && objective > 0 || throw(ArgumentError("$(context) has an invalid scalar"))
        _s04_matches(eta, inv(eta_c)) || throw(ArgumentError("$(context) has inconsistent eta and eta_c"))
        push!(keys, _s04_key(eta_c))
    end
    length(unique(keys)) == 26 || throw(ArgumentError("$(context) contains a duplicate eta_c"))
    count(row -> row["selected"] === true, rows) == 1 || throw(ArgumentError(
        "$(context) must contain exactly one selected row",
    ))
    return nothing
end

function _s04_validate_aggregate_jld(jld_path, summaries, curves_by_N)
    payload = load_jld(jld_path)
    required_keys = Set([
        "format",
        "finite_horizon_relaxation",
        "decision",
        "required_horizons",
        "curve_rows",
        "summary_rows",
        "selected_results",
    ])
    issubset(required_keys, Set(keys(payload))) || throw(ArgumentError("aggregate JLD is missing required datasets"))
    payload["format"] == "JLD2" || throw(ArgumentError("aggregate JLD has an unexpected format label"))
    payload["finite_horizon_relaxation"] === true || throw(ArgumentError("aggregate JLD lost its relaxation label"))
    payload["decision"] == "COMPLETE" || throw(ArgumentError("aggregate JLD is not COMPLETE"))
    Int.(payload["required_horizons"]) == S04_HORIZONS || throw(ArgumentError(
        "aggregate JLD horizon list is not exactly N=5:30",
    ))

    jld_summaries = payload["summary_rows"]
    length(jld_summaries) == 26 || throw(ArgumentError("aggregate JLD must contain 26 summaries"))
    jld_summary_by_N = Dict(Int(row["N"]) => row for row in jld_summaries)
    sort(collect(keys(jld_summary_by_N))) == S04_HORIZONS || throw(ArgumentError(
        "aggregate JLD summary horizons are not exact",
    ))
    summary_by_N = Dict(parse(Int, row["N"]) => row for row in summaries)

    jld_curve_rows = payload["curve_rows"]
    length(jld_curve_rows) == 676 || throw(ArgumentError("aggregate JLD must contain exactly 676 curve rows"))
    selected_results = payload["selected_results"]
    Set(string.(S04_HORIZONS)) == Set(string.(keys(selected_results))) || throw(ArgumentError(
        "aggregate JLD selected-result horizon keys are not exact",
    ))

    for N in S04_HORIZONS
        csv_summary = summary_by_N[N]
        jld_summary = jld_summary_by_N[N]
        jld_summary["classification"] == "flat" || throw(ArgumentError("aggregate JLD N=$(N) is not flat"))
        jld_summary["decision"] == "COMPLETE" || throw(ArgumentError("aggregate JLD N=$(N) is not COMPLETE"))
        Int(jld_summary["num_solves"]) == 26 || throw(ArgumentError("aggregate JLD N=$(N) solve count is not 26"))

        jld_curve = [row for row in jld_curve_rows if Int(row["N"]) == N]
        _s04_validate_jld_curve_rows(jld_curve, N)
        csv_curve = curves_by_N[N]
        jld_by_key = Dict(_s04_key(row["eta_c"]) => row for row in jld_curve)
        for csv_row in csv_curve
            eta_c = _s04_parse_float(csv_row, "eta_c", "sweep curve N=$(N)")
            key = _s04_key(eta_c)
            haskey(jld_by_key, key) || throw(ArgumentError("aggregate JLD N=$(N) is missing eta_c=$(eta_c)"))
            jld_row = jld_by_key[key]
            for field in ("eta", "objective", "pfeas_tolerance", "dfeas_tolerance", "solve_seconds")
                csv_value = _s04_parse_float(csv_row, field, "sweep curve N=$(N)")
                _s04_matches(csv_value, jld_row[field]) || throw(ArgumentError(
                    "aggregate JLD N=$(N) $(field) disagrees with its curve CSV",
                ))
            end
            for field in ("search_phase", "termination_status", "primal_status", "dual_status", "solver")
                csv_row[field] == jld_row[field] || throw(ArgumentError(
                    "aggregate JLD N=$(N) $(field) disagrees with its curve CSV",
                ))
            end
            (csv_row["selected"] == "true") == (jld_row["selected"] === true) || throw(ArgumentError(
                "aggregate JLD N=$(N) selection flag disagrees with its curve CSV",
            ))
        end

        selected_csv = only(filter(row -> row["selected"] == "true", csv_curve))
        selected_payload = selected_results[string(N)]
        for (curve_field, summary_field) in (
            ("eta_c", "selected_eta_c"),
            ("eta", "selected_eta"),
            ("objective", "selected_objective"),
        )
            csv_value = _s04_parse_float(selected_csv, curve_field, "sweep curve N=$(N)")
            _s04_matches(csv_value, Float64(jld_summary[summary_field])) || throw(ArgumentError(
                "aggregate JLD N=$(N) summary $(summary_field) disagrees with the curve CSV",
            ))
            _s04_matches(csv_value, Float64(selected_payload[curve_field])) || throw(ArgumentError(
                "aggregate JLD N=$(N) selected payload $(curve_field) disagrees with the curve CSV",
            ))
            _s04_matches(csv_value, _s04_parse_float(csv_summary, summary_field, "sweep summary N=$(N)")) || throw(ArgumentError(
                "aggregate JLD N=$(N) disagrees with the summary CSV",
            ))
        end
        selected_payload["termination_status"] == "OPTIMAL" || throw(ArgumentError("aggregate JLD N=$(N) selected payload is non-OPTIMAL"))
        selected_payload["primal_status"] == "FEASIBLE_POINT" || throw(ArgumentError("aggregate JLD N=$(N) selected payload has non-feasible primal status"))
        selected_payload["dual_status"] == "FEASIBLE_POINT" || throw(ArgumentError("aggregate JLD N=$(N) selected payload has non-feasible dual status"))
        selected_payload["solver"] == "mosek" || throw(ArgumentError("aggregate JLD N=$(N) selected payload is not MOSEK"))
        _s04_matches(selected_payload["pfeas_tolerance"], S04_PFEAS_TOLERANCE) || throw(ArgumentError("aggregate JLD N=$(N) selected payload has a noncanonical primal tolerance"))
        _s04_matches(selected_payload["dfeas_tolerance"], S04_DFEAS_TOLERANCE) || throw(ArgumentError("aggregate JLD N=$(N) selected payload has a noncanonical dual tolerance"))
    end
    return nothing
end

function _s04_validate_ergodic_archive(path)
    _s04_require_header(path, S04_PEP_EXPORT_HEADER)
    rows = read_simple_csv(path)
    length(rows) == 46 || throw(ArgumentError("archived ergodic CSV must contain T=5:50"))
    horizons = [_s04_parse_int(row, "T", "archived ergodic CSV") for row in rows]
    horizons == collect(5:50) || throw(ArgumentError("archived ergodic CSV horizons must be the ordered set T=5:50"))
    for row in rows
        eta = _s04_parse_float(row, "optimized_eta", "archived ergodic CSV")
        gap = _s04_parse_float(row, "optimized_duality_gap", "archived ergodic CSV")
        eta > 0 && gap > 0 || throw(ArgumentError("archived ergodic CSV contains a nonpositive value"))
    end
    return rows[1:length(S04_HORIZONS)]
end

function validate_s04_inputs(; sweep_summary, curve_dir, sweep_jld, ergodic_csv)
    _s04_require_header(sweep_summary, S04_SUMMARY_HEADER)
    summaries = read_simple_csv(sweep_summary)
    _s04_validate_summary_rows(summaries)

    observed_curve_files = filter(
        name -> match(r"^sweep_lst_eta_curve_N\d+\.csv$", name) !== nothing,
        readdir(curve_dir),
    )
    expected_curve_files = ["sweep_lst_eta_curve_N$(N).csv" for N in S04_HORIZONS]
    sort(observed_curve_files) == sort(expected_curve_files) || throw(ArgumentError(
        "curve directory must contain exactly the N=5:30 sweep curve-file set",
    ))

    curves_by_N = Dict{Int,Vector{Dict{String,String}}}()
    selected_rows = NamedTuple[]
    for (N, summary) in zip(S04_HORIZONS, summaries)
        path = joinpath(curve_dir, "sweep_lst_eta_curve_N$(N).csv")
        _s04_require_header(path, S04_CURVE_HEADER)
        curve = read_simple_csv(path)
        selected = _s04_validate_curve_rows(curve, N, summary)
        curves_by_N[N] = curve
        push!(selected_rows, (
            T = N,
            eta_c = _s04_parse_float(selected, "eta_c", "sweep curve N=$(N)"),
            eta = _s04_parse_float(selected, "eta", "sweep curve N=$(N)"),
            gap = _s04_parse_float(selected, "objective", "sweep curve N=$(N)"),
        ))
    end
    sum(length, values(curves_by_N)) == 676 || throw(ArgumentError("sweep curves must contain exactly 676 rows"))
    _s04_validate_aggregate_jld(sweep_jld, summaries, curves_by_N)

    ergodic_rows = _s04_validate_ergodic_archive(ergodic_csv)
    ergodic = NamedTuple[]
    for (selected, row) in zip(selected_rows, ergodic_rows)
        T = _s04_parse_int(row, "T", "archived ergodic CSV")
        T == selected.T || throw(ArgumentError("ergodic/last-iterate horizon join is not exact"))
        eta = _s04_parse_float(row, "optimized_eta", "archived ergodic CSV T=$(T)")
        gap = _s04_parse_float(row, "optimized_duality_gap", "archived ergodic CSV T=$(T)")
        abs(selected.eta - eta) <= S04_ROUNDED_ETA_TOLERANCE || throw(ArgumentError(
            "last-iterate canonical eta at T=$(T) does not match the rounded archived ergodic eta",
        ))
        push!(ergodic, (T = T, eta = eta, gap = gap))
    end
    return (last_iterate = selected_rows, ergodic = ergodic)
end

function fit_loglog(T_values, gap_values)
    length(T_values) == length(gap_values) || throw(ArgumentError("fit inputs must have equal lengths"))
    length(T_values) >= 3 || throw(ArgumentError("a log-log fit needs at least three points"))
    T = Float64.(collect(T_values))
    gaps = Float64.(collect(gap_values))
    all(isfinite.(T)) && all(T .> 0) || throw(ArgumentError("fit horizons must be finite and positive"))
    all(isfinite.(gaps)) && all(gaps .> 0) || throw(ArgumentError("fit gaps must be finite and positive"))

    x = log.(T)
    y = log.(gaps)
    x_mean = mean(x)
    y_mean = mean(y)
    denominator = sum((value - x_mean)^2 for value in x)
    denominator > 0 || throw(ArgumentError("fit horizons must not all be equal"))
    slope = sum((x[index] - x_mean) * (y[index] - y_mean) for index in eachindex(x)) / denominator
    intercept = y_mean - slope * x_mean
    fitted_log = intercept .+ slope .* x
    residuals = y .- fitted_log
    sse = sum(abs2, residuals)
    sst = sum(abs2, y .- y_mean)
    constant_scale = max(1.0, sum(abs2, y))
    r_squared = sst <= eps(Float64)^2 * constant_scale ? nothing : 1.0 - sse / sst
    rmse = sqrt(sse / length(T))
    slope_standard_error = length(T) > 2 ? sqrt((sse / (length(T) - 2)) / denominator) : nothing
    fitted = exp.(fitted_log)
    max_relative_fit_error = maximum(abs.(fitted .- gaps) ./ gaps)
    return (
        intercept = intercept,
        slope = slope,
        prefactor = exp(intercept),
        sse_log = sse,
        sst_log = sst,
        r_squared = r_squared,
        rmse_log = rmse,
        slope_standard_error = slope_standard_error,
        max_relative_fit_error = max_relative_fit_error,
        log_T = x,
        log_gap = y,
        fitted_log_gap = fitted_log,
        fitted_gap = fitted,
        log_residual = residuals,
    )
end

function _s04_fit_rows(series_data)
    summaries = NamedTuple[]
    points = NamedTuple[]
    fit_by_key = Dict{Tuple{String,String},Any}()
    for (series_name, data) in series_data
        for window in S04_FIT_WINDOWS
            window_data = filter(row -> window.T_min <= row.T <= window.T_max, data)
            fit = fit_loglog([row.T for row in window_data], [row.gap for row in window_data])
            fit_by_key[(series_name, window.name)] = fit
            push!(summaries, (
                series = series_name,
                window = window.name,
                T_min = window.T_min,
                T_max = window.T_max,
                n = length(window_data),
                log_base = "natural",
                intercept = fit.intercept,
                slope = fit.slope,
                prefactor = fit.prefactor,
                sse_log = fit.sse_log,
                sst_log = fit.sst_log,
                r_squared = fit.r_squared,
                rmse_log = fit.rmse_log,
                slope_standard_error = fit.slope_standard_error,
                max_relative_fit_error = fit.max_relative_fit_error,
            ))
            for (index, row) in enumerate(window_data)
                push!(points, (
                    series = series_name,
                    window = window.name,
                    T = row.T,
                    duality_gap = row.gap,
                    log_T = fit.log_T[index],
                    log_gap = fit.log_gap[index],
                    fitted_log_gap = fit.fitted_log_gap[index],
                    fitted_gap = fit.fitted_gap[index],
                    log_residual = fit.log_residual[index],
                ))
            end
        end
    end
    return summaries, points, fit_by_key
end

function _s04_build_outputs(inputs)
    last_iterate_export = [(
        T = row.T,
        optimized_eta = row.eta,
        optimized_duality_gap = row.gap,
    ) for row in inputs.last_iterate]

    ergodic_by_T = Dict(row.T => row for row in inputs.ergodic)
    last_by_T = Dict(row.T => row for row in inputs.last_iterate)
    ergodic_gap_at_5 = ergodic_by_T[5].gap
    last_gap_at_5 = last_by_T[5].gap
    gap_figure = [(
        T = T,
        ergodic_duality_gap = ergodic_by_T[T].gap,
        last_iterate_duality_gap = last_by_T[T].gap,
        guide_T_minus_1 = ergodic_gap_at_5 * 5 / T,
        guide_T_minus_half = last_gap_at_5 * sqrt(5 / T),
    ) for T in S04_HORIZONS]
    eta_figure = [(
        T = T,
        ergodic_optimized_eta = ergodic_by_T[T].eta,
        last_iterate_selected_eta = last_by_T[T].eta,
        absolute_eta_difference = abs(ergodic_by_T[T].eta - last_by_T[T].eta),
    ) for T in S04_HORIZONS]

    fit_summaries, fit_points, fit_by_key = _s04_fit_rows([
        ("ergodic_average", inputs.ergodic),
        ("last_iterate", inputs.last_iterate),
    ])
    return (
        last_iterate_export = last_iterate_export,
        gap_figure = gap_figure,
        eta_figure = eta_figure,
        fit_summaries = fit_summaries,
        fit_points = fit_points,
        fit_by_key = fit_by_key,
    )
end

function _s04_output_specs(outputs)
    return [
        ("pep_lastiterate_optimized_stepsizes_altgda.csv", S04_PEP_EXPORT_HEADER, outputs.last_iterate_export),
        ("pep_ergodic_lastiterate_gap_figure_data.csv", S04_GAP_FIGURE_HEADER, outputs.gap_figure),
        ("pep_ergodic_lastiterate_eta_figure_data.csv", S04_ETA_FIGURE_HEADER, outputs.eta_figure),
        ("pep_ergodic_lastiterate_loglog_fit_summary.csv", S04_FIT_SUMMARY_HEADER, outputs.fit_summaries),
        ("pep_ergodic_lastiterate_loglog_fit_points.csv", S04_FIT_POINTS_HEADER, outputs.fit_points),
    ]
end

_s04_requires_narrative_decision(slope::Real) =
    abs(Float64(slope) + 1.0) <= S04_NEAR_MINUS_ONE_TOLERANCE

function _s04_validate_output_bundle(directory, outputs)
    for (filename, header, _) in _s04_output_specs(outputs)
        path = joinpath(directory, filename)
        _s04_require_header(path, header)
    end
    export_rows = read_simple_csv(joinpath(directory, "pep_lastiterate_optimized_stepsizes_altgda.csv"))
    [_s04_parse_int(row, "T", "last-iterate export") for row in export_rows] == S04_HORIZONS || throw(ArgumentError(
        "last-iterate export does not contain exactly T=5:30",
    ))
    length(export_rows) == 26 || throw(ArgumentError("last-iterate export must contain 26 rows"))
    for (saved, source) in zip(export_rows, outputs.last_iterate_export)
        _s04_matches(_s04_parse_float(saved, "optimized_eta", "last-iterate export"), source.optimized_eta) || throw(ArgumentError("last-iterate eta export lost source precision"))
        _s04_matches(_s04_parse_float(saved, "optimized_duality_gap", "last-iterate export"), source.optimized_duality_gap) || throw(ArgumentError("last-iterate gap export lost source precision"))
    end

    gap_rows = read_simple_csv(joinpath(directory, "pep_ergodic_lastiterate_gap_figure_data.csv"))
    length(gap_rows) == 26 || throw(ArgumentError("gap figure data must contain 26 rows"))
    inverse_constants = Float64[]
    inverse_sqrt_constants = Float64[]
    for row in gap_rows
        T = _s04_parse_int(row, "T", "gap figure data")
        push!(inverse_constants, T * _s04_parse_float(row, "guide_T_minus_1", "gap figure data"))
        push!(inverse_sqrt_constants, sqrt(T) * _s04_parse_float(row, "guide_T_minus_half", "gap figure data"))
    end
    maximum(inverse_constants) - minimum(inverse_constants) <= 1e-12 || throw(ArgumentError("T^-1 guide is not invariant"))
    maximum(inverse_sqrt_constants) - minimum(inverse_sqrt_constants) <= 1e-12 || throw(ArgumentError("T^-1/2 guide is not invariant"))

    eta_rows = read_simple_csv(joinpath(directory, "pep_ergodic_lastiterate_eta_figure_data.csv"))
    length(eta_rows) == 26 || throw(ArgumentError("eta figure data must contain 26 rows"))
    fit_summary_rows = read_simple_csv(joinpath(directory, "pep_ergodic_lastiterate_loglog_fit_summary.csv"))
    length(fit_summary_rows) == 4 || throw(ArgumentError("fit summary must contain four predeclared fits"))
    fit_point_rows = read_simple_csv(joinpath(directory, "pep_ergodic_lastiterate_loglog_fit_points.csv"))
    length(fit_point_rows) == 84 || throw(ArgumentError("fit-point data must contain 84 rows"))

    for summary in fit_summary_rows
        series = summary["series"]
        window_name = summary["window"]
        window = only(filter(candidate -> candidate.name == window_name, S04_FIT_WINDOWS))
        points = filter(
            row -> row["series"] == series && row["window"] == window_name,
            fit_point_rows,
        )
        expected_count = window.T_max - window.T_min + 1
        length(points) == expected_count || throw(ArgumentError("fit-point count is inconsistent"))
        recomputed = fit_loglog(
            [_s04_parse_int(row, "T", "fit points") for row in points],
            [_s04_parse_float(row, "duality_gap", "fit points") for row in points],
        )
        saved_slope = _s04_parse_float(summary, "slope", "fit summary")
        saved_intercept = _s04_parse_float(summary, "intercept", "fit summary")
        _s04_matches(saved_slope, recomputed.slope; rtol = 5e-12, atol = 1e-14) || throw(ArgumentError("saved slope does not reproduce"))
        _s04_matches(saved_intercept, recomputed.intercept; rtol = 5e-12, atol = 1e-14) || throw(ArgumentError("saved intercept does not reproduce"))
    end
    return nothing
end

function export_lastiterate_figures(; sweep_summary, curve_dir, sweep_jld, ergodic_csv, output_dir)
    inputs = validate_s04_inputs(
        sweep_summary = sweep_summary,
        curve_dir = curve_dir,
        sweep_jld = sweep_jld,
        ergodic_csv = ergodic_csv,
    )
    outputs = _s04_build_outputs(inputs)
    tail_last_fit = outputs.fit_by_key[("last_iterate", S04_TAIL_WINDOW.name)]
    narrative_contingency = _s04_requires_narrative_decision(tail_last_fit.slope)

    mkpath(output_dir)
    mktempdir(; prefix = "iclr27-s04-stage-") do staging_dir
        for (filename, header, rows) in _s04_output_specs(outputs)
            write_csv_atomic(joinpath(staging_dir, filename), header, rows)
        end
        _s04_validate_output_bundle(staging_dir, outputs)
        for (filename, _, _) in _s04_output_specs(outputs)
            promote_file(joinpath(staging_dir, filename), joinpath(output_dir, filename))
        end
    end


    if narrative_contingency
        throw(S04NarrativeContingency(
            "last-iterate tail slope $(tail_last_fit.slope) is unexpectedly near -1; " *
            "the derived diagnostics were preserved, and the predeclared narrative " *
            "contingency requires a user decision before manuscript work",
        ))
    end

    println("ICLR27-S04 EXPORT: COMPLETE")
    for summary in outputs.fit_summaries
        @printf(
            "%s %s: slope=%.12g R2=%s\n",
            summary.series,
            summary.window,
            summary.slope,
            summary.r_squared === nothing ? "undefined" : @sprintf("%.12g", summary.r_squared),
        )
    end
    println("Interpretation gate: PASS (last-iterate tail slope is not near -1)")
    return outputs
end


function _s04_parse_cli(arguments)
    defaults = Dict(
        "sweep-summary" => joinpath(@__DIR__, "Data", "sweep_lst_summary.csv"),
        "curve-dir" => joinpath(@__DIR__, "Data"),
        "sweep-jld" => joinpath(@__DIR__, "Data", "AltGDA_lst_5_30.jld"),
        "ergodic-csv" => joinpath(@__DIR__, "Data", "pep_optimized_stepsizes_altgda.csv"),
        "output-dir" => joinpath(@__DIR__, "Data"),
    )
    index = 1
    while index <= length(arguments)
        argument = arguments[index]
        startswith(argument, "--") || throw(ArgumentError("unexpected positional argument: $(argument)"))
        name = argument[3:end]
        haskey(defaults, name) || throw(ArgumentError("unknown option --$(name)"))
        index < length(arguments) || throw(ArgumentError("option --$(name) requires a value"))
        defaults[name] = arguments[index + 1]
        index += 2
    end
    return (
        sweep_summary = abspath(defaults["sweep-summary"]),
        curve_dir = abspath(defaults["curve-dir"]),
        sweep_jld = abspath(defaults["sweep-jld"]),
        ergodic_csv = abspath(defaults["ergodic-csv"]),
        output_dir = abspath(defaults["output-dir"]),
    )
end

function s04_main(arguments = ARGS)
    options = _s04_parse_cli(arguments)
    export_lastiterate_figures(; options...)
    return 0
end

if abspath(PROGRAM_FILE) == @__FILE__
    exit(s04_main())
end
