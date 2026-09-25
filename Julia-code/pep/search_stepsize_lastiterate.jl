
using Dates
using OffsetArrays
using Printf
using Statistics

include(joinpath(@__DIR__, "sdp.jl"))
include(joinpath(@__DIR__, "csv.jl"))

const DEFAULT_ETA_C_LO = 0.5
const DEFAULT_ETA_C_HI = 64.0
const DEFAULT_GRID_POINTS = 25
const DEFAULT_FLAT_TOLERANCE = 1e-3
const DEFAULT_RELATIVE_BRACKET_TOLERANCE = 1e-2
const DEFAULT_MAX_WIDENINGS = 3
const DEFAULT_PFEAS_TOLERANCE = 1e-4
const DEFAULT_DFEAS_TOLERANCE = 1e-4
const DEFAULT_SESSION_SECONDS = 3 * 60 * 60
const DEFAULT_VALIDATION_SECONDS = 5 * 60 * 60 / 2
const SWEEP_HORIZONS = collect(5:30)
const PERMITTED_SEARCH_CLASSIFICATIONS = Set([
    "interior",
    "boundary_lower",
    "boundary_upper",
    "flat",
])

const VALIDATION_REFERENCES = Dict(
    5 => (eta = 1.527, objective = 0.614),
    10 => (eta = 1.370, objective = 0.345),
    30 => (eta = 1.249, objective = 0.130),
)

const ARCHIVED_ERGODIC_ETA = Dict(
    5 => 1.5269322725172283,
    6 => 1.3891427526960336,
    7 => 1.6318467781761963,
    8 => 1.5739225878600864,
    9 => 1.466586904922715,
    10 => 1.3701099693528032,
    11 => 1.3042732109147075,
    12 => 1.516875237011756,
    13 => 1.4537942116035734,
    14 => 1.3765622169896756,
    15 => 1.3141967836762927,
    16 => 1.2618296529968454,
    17 => 1.4384404277467588,
    18 => 1.3871144369410477,
    19 => 1.3326319480974929,
    20 => 1.2827004219409284,
    21 => 1.2391977824881786,
    22 => 1.38863511785127,
    23 => 1.3468013468013467,
    24 => 1.3024850042844902,
    25 => 1.263087917566894,
    26 => 1.228779304769604,
    27 => 1.3554485464597825,
    28 => 1.319215413990627,
    29 => 1.2827004219409284,
    30 => 1.2493835278645404,
)

const CURVE_HEADER = [
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

const SUMMARY_HEADER = [
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

const SHARD_HEADER = [
    "range_group",
    "shard_index",
    "start_N",
    "end_N",
    "predicted_seconds",
    "predicted_hours",
    "over_two_hours",
    "fit_exponent",
    "fit_scale",
    "predicted_solves_per_N",
    "safety_factor",
    "plan_source",
]

struct TimeboxExpired <: Exception
    message::String
end

Base.showerror(io::IO, error::TimeboxExpired) = print(io, error.message)

struct StrictStatusFailure <: Exception
    message::String
end

Base.showerror(io::IO, error::StrictStatusFailure) = print(io, error.message)

"""Return n logarithmically spaced points, preserving the exact endpoints."""
function log_grid(lo::Real, hi::Real, n::Integer = DEFAULT_GRID_POINTS)
    lo > 0 || throw(ArgumentError("the lower log-grid endpoint must be positive"))
    hi > lo || throw(ArgumentError("the upper log-grid endpoint must exceed the lower endpoint"))
    n >= 2 || throw(ArgumentError("a log grid needs at least two points"))
    grid = exp.(range(log(Float64(lo)), log(Float64(hi)); length = Int(n)))
    grid[1] = Float64(lo)
    grid[end] = Float64(hi)
    return grid
end

_cache_key(eta_c::Real) = @sprintf("%.14g", Float64(eta_c))

function _raw_field(raw, name::Symbol, default = nothing)
    if raw isa AbstractDict
        haskey(raw, name) && return raw[name]
        haskey(raw, string(name)) && return raw[string(name)]
        return default
    end
    return hasproperty(raw, name) ? getproperty(raw, name) : default
end

function _objective_available(row)
    objective = row["objective"]
    return objective isa Real && isfinite(objective)
end

function strict_status_success(row)
    return _objective_available(row) &&
           row["termination_status"] == "OPTIMAL" &&
           row["primal_status"] == "FEASIBLE_POINT" &&
           row["dual_status"] == "FEASIBLE_POINT"
end

function _tolerance_matches(value, expected)
    value isa Real || return false
    return isfinite(value) && isapprox(Float64(value), Float64(expected); rtol = 1e-12, atol = 0.0)
end

function _checkpoint_rows_valid(
    rows;
    N,
    performance_measure,
    solver,
    pfeas_tolerance = DEFAULT_PFEAS_TOLERANCE,
    dfeas_tolerance = DEFAULT_DFEAS_TOLERANCE,
)
    required_fields = (
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
    )
    keys_seen = Set{String}()
    for (index, row) in enumerate(rows)
        all(haskey(row, field) for field in required_fields) ||
            return false, "checkpoint row $index is missing a required field"
        row["N"] isa Integer && Int(row["N"]) == N ||
            return false, "checkpoint row $index has the wrong horizon"
        row["performance_measure"] == String(performance_measure) ||
            return false, "checkpoint row $index has the wrong performance measure"
        row["solver"] == String(solver) ||
            return false, "checkpoint row $index has the wrong solver"
        row["search_phase"] isa AbstractString && !isempty(row["search_phase"]) ||
            return false, "checkpoint row $index has invalid search-phase metadata"
        row["search_round"] isa Integer && row["search_round"] >= 0 ||
            return false, "checkpoint row $index has invalid search-round metadata"
        _tolerance_matches(row["pfeas_tolerance"], pfeas_tolerance) ||
            return false, "checkpoint row $index has the wrong primal tolerance"
        _tolerance_matches(row["dfeas_tolerance"], dfeas_tolerance) ||
            return false, "checkpoint row $index has the wrong dual tolerance"
        row["eta_c"] isa Real && isfinite(row["eta_c"]) && row["eta_c"] > 0 ||
            return false, "checkpoint row $index has invalid eta_c"
        row["eta"] isa Real && isfinite(row["eta"]) && row["eta"] > 0 ||
            return false, "checkpoint row $index has invalid eta"
        isapprox(Float64(row["eta"]), inv(Float64(row["eta_c"])); rtol = 1e-12, atol = 0.0) ||
            return false, "checkpoint row $index has inconsistent eta and eta_c"
        all(
            row[field] isa AbstractString && !isempty(row[field])
            for field in ("termination_status", "primal_status", "dual_status")
        ) || return false, "checkpoint row $index has an invalid solver status"
        row["objective"] === nothing ||
            (row["objective"] isa Real && isfinite(row["objective"])) ||
            return false, "checkpoint row $index has an invalid objective field"
        row["solve_seconds"] isa Real && isfinite(row["solve_seconds"]) && row["solve_seconds"] >= 0 ||
            return false, "checkpoint row $index has invalid solve time"
        row["selected"] isa Bool ||
            return false, "checkpoint row $index has invalid selection metadata"
        key = _cache_key(Float64(row["eta_c"]))
        key in keys_seen && return false, "checkpoint contains a duplicate eta_c"
        push!(keys_seen, key)
    end
    return true, "checkpoint rows passed semantic validation"
end

function _record_from_raw(
    raw,
    eta_c::Real,
    search_phase::AbstractString,
    search_round::Integer;
    N::Integer,
    performance_measure::Symbol,
)
    objective = _raw_field(raw, :objective)
    objective = objective isa Real ? Float64(objective) : nothing
    return Dict{String,Any}(
        "N" => Int(N),
        "performance_measure" => String(performance_measure),
        "search_phase" => String(search_phase),
        "search_round" => Int(search_round),
        "eta_c" => Float64(eta_c),
        "eta" => inv(Float64(eta_c)),
        "objective" => objective,
        "termination_status" => string(_raw_field(raw, :termination_status, "UNKNOWN")),
        "primal_status" => string(_raw_field(raw, :primal_status, "UNKNOWN")),
        "dual_status" => string(_raw_field(raw, :dual_status, "UNKNOWN")),
        "solver" => string(_raw_field(raw, :solver, "unknown")),
        "pfeas_tolerance" => _raw_field(raw, :pfeas_tolerance),
        "dfeas_tolerance" => _raw_field(raw, :dfeas_tolerance),
        "solve_seconds" => Float64(_raw_field(raw, :solve_seconds, 0.0)),
        "selected" => false,
    )
end

function _raw_from_record(row)
    return (
        objective = row["objective"],
        G_xv = nothing,
        G_uy = nothing,
        nu = nothing,
        termination_status = row["termination_status"],
        primal_status = row["primal_status"],
        dual_status = row["dual_status"],
        solve_seconds = row["solve_seconds"],
        solver = Symbol(row["solver"]),
        pfeas_tolerance = row["pfeas_tolerance"],
        dfeas_tolerance = row["dfeas_tolerance"],
    )
end

function _neighbor_bounds(rows, selected_eta_c::Real)
    points = sort(unique(Float64(row["eta_c"]) for row in rows))
    index = findfirst(point -> isapprox(point, selected_eta_c; rtol = 2e-13, atol = 0.0), points)
    index === nothing && error("the selected eta_c is absent from the evaluated cache")
    if length(points) == 1
        return points[1], points[1]
    elseif index == 1
        return points[1], points[2]
    elseif index == length(points)
        return points[end - 1], points[end]
    end
    return points[index - 1], points[index + 1]
end

function _selected_cache_entry(cache, eta_c::Real)
    key = _cache_key(eta_c)
    haskey(cache, key) || error("selected point is missing from the cache")
    return cache[key]
end

function _finish_search!(
    rows,
    cache,
    classification::AbstractString,
    selected_eta_c,
    widenings::Integer,
    checkpoint_callback::Function;
    N::Integer,
    performance_measure::Symbol,
    solver::Symbol,
)
    for row in rows
        row["selected"] = false
    end

    selected_payload = nothing
    selected_eta = nothing
    selected_objective = nothing
    final_lo = nothing
    final_hi = nothing
    eta_spacing = nothing
    if selected_eta_c !== nothing
        entry = _selected_cache_entry(cache, selected_eta_c)
        rows[entry.row_index]["selected"] = true
        selected_payload = entry.raw
        selected_eta = inv(Float64(selected_eta_c))
        selected_objective = rows[entry.row_index]["objective"]
        final_lo, final_hi = _neighbor_bounds(rows, Float64(selected_eta_c))
        eta_spacing = max(
            abs(selected_eta - inv(final_lo)),
            abs(selected_eta - inv(final_hi)),
        )
    end

    all_optimal = !isempty(rows) && all(strict_status_success, rows)
    summary = Dict{String,Any}(
        "N" => Int(N),
        "performance_measure" => String(performance_measure),
        "solver" => String(solver),
        "classification" => String(classification),
        "selected_eta_c" => selected_eta_c,
        "selected_eta" => selected_eta,
        "selected_objective" => selected_objective,
        "all_optimal" => all_optimal,
        "num_solves" => length(rows),
        "total_solve_seconds" => sum(
            (Float64(row["solve_seconds"]) for row in rows);
            init = 0.0,
        ),
        "final_eta_c_lo" => final_lo,
        "final_eta_c_hi" => final_hi,
        "boundary_widenings" => Int(widenings),
        "eta_grid_spacing" => eta_spacing,
        "validation_reference_eta" => nothing,
        "validation_reference_objective" => nothing,
        "validation_objective_error" => nothing,
        "validation_eta_match" => nothing,
        "validation_pass" => nothing,
        "decision" => "",
        "decision_reason" => "",
    )
    checkpoint_callback(rows)
    return (
        rows = rows,
        summary = summary,
        selected_payload = selected_payload,
        cache = cache,
    )
end

"""
    search_eta_c(evaluator; canonical_eta, ...)

Minimize the evaluator's SDP objective over eta_c using the S01 cached search.
The evaluator is called once per distinct eta_c and must return the named
solver-result interface used by solve_primal_with_known_stepsizes.
"""
function search_eta_c(
    evaluator::Function;
    canonical_eta::Real,
    N::Integer = 0,
    performance_measure::Symbol = :avg,
    solver::Symbol = :mosek,
    initial_lo::Real = DEFAULT_ETA_C_LO,
    initial_hi::Real = DEFAULT_ETA_C_HI,
    num_points::Integer = DEFAULT_GRID_POINTS,
    flat_tolerance::Real = DEFAULT_FLAT_TOLERANCE,
    relative_bracket_tolerance::Real = DEFAULT_RELATIVE_BRACKET_TOLERANCE,
    max_widenings::Integer = DEFAULT_MAX_WIDENINGS,
    checkpoint_callback::Function = rows -> nothing,
    deadline::Real = Inf,
    initial_rows = Dict{String,Any}[],
    abort_on_non_strict::Bool = false,
)
    canonical_eta > 0 || throw(ArgumentError("canonical_eta must be positive"))
    flat_tolerance >= 0 || throw(ArgumentError("flat_tolerance must be nonnegative"))
    relative_bracket_tolerance > 0 || throw(ArgumentError("relative bracket tolerance must be positive"))
    max_widenings >= 0 || throw(ArgumentError("max_widenings must be nonnegative"))

    rows = Dict{String,Any}[
        Dict{String,Any}(string(key) => value for (key, value) in pairs(source_row))
        for source_row in initial_rows
    ]
    cache = Dict{String,Any}()
    for (row_index, row) in enumerate(rows)
        row["selected"] = false
        key = _cache_key(Float64(row["eta_c"]))
        haskey(cache, key) && throw(ArgumentError("initial_rows contains duplicate eta_c points"))
        cache[key] = (row_index = row_index, raw = _raw_from_record(row))
    end
    widenings = 0
    if abort_on_non_strict && any(!strict_status_success(row) for row in rows)
        return _finish_search!(
            rows, cache, "solver_failure", nothing, widenings, checkpoint_callback;
            N = N, performance_measure = performance_measure, solver = solver,
        )
    end

    function evaluate_point!(eta_c, phase, round)
        key = _cache_key(eta_c)
        haskey(cache, key) && return cache[key]
        time() < deadline || throw(TimeboxExpired("the PEP experiment timebox expired before the next SDP solve"))
        raw = evaluator(Float64(eta_c))
        row = _record_from_raw(
            raw,
            Float64(eta_c),
            phase,
            round;
            N = N,
            performance_measure = performance_measure,
        )
        push!(rows, row)
        entry = (row_index = length(rows), raw = raw)
        cache[key] = entry
        checkpoint_callback(rows)
        if abort_on_non_strict && !strict_status_success(row)
            status_triple = join((
                row["termination_status"],
                row["primal_status"],
                row["dual_status"],
            ), "/")
            throw(StrictStatusFailure(
                "non-strict solver status at N=$N, eta_c=$(Float64(eta_c)): " *
                status_triple,
            ))
        end
        return entry
    end

    function evaluate_grid!(grid, phase, round)
        for eta_c in grid
            evaluate_point!(eta_c, phase, round)
        end
        return nothing
    end

    function best_row()
        candidates = filter(_objective_available, rows)
        isempty(candidates) && return nothing
        return candidates[argmin(Float64(row["objective"]) for row in candidates)]
    end

    function cache_is_numerically_complete()
        return !isempty(rows) && all(_objective_available, rows)
    end

    lo = Float64(initial_lo)
    hi = Float64(initial_hi)

    try
        round = 0
        while true
            phase = round == 0 ? "coarse" : "widen"
            grid = log_grid(lo, hi, num_points)
            evaluate_grid!(grid, phase, round)
            if !cache_is_numerically_complete()
                return _finish_search!(
                    rows, cache, "solver_failure", nothing, widenings, checkpoint_callback;
                    N = N, performance_measure = performance_measure, solver = solver,
                )
            end

            grid_rows = [_selected_cache_entry(cache, point) for point in grid]
            grid_objectives = [Float64(rows[entry.row_index]["objective"]) for entry in grid_rows]
            if maximum(grid_objectives) - minimum(grid_objectives) < flat_tolerance
                canonical_eta_c = inv(Float64(canonical_eta))
                evaluate_point!(canonical_eta_c, "canonical_flat", round)
                return _finish_search!(
                    rows, cache, "flat", canonical_eta_c, widenings, checkpoint_callback;
                    N = N, performance_measure = performance_measure, solver = solver,
                )
            end

            best_index = argmin(grid_objectives)
            if best_index == 1
                if widenings < max_widenings
                    lo /= 4
                    widenings += 1
                    round += 1
                    continue
                end
                return _finish_search!(
                    rows, cache, "boundary_lower", grid[1], widenings, checkpoint_callback;
                    N = N, performance_measure = performance_measure, solver = solver,
                )
            elseif best_index == length(grid)
                if widenings < max_widenings
                    hi *= 4
                    widenings += 1
                    round += 1
                    continue
                end
                return _finish_search!(
                    rows, cache, "boundary_upper", grid[end], widenings, checkpoint_callback;
                    N = N, performance_measure = performance_measure, solver = solver,
                )
            end
            break
        end

        refinement_round = 1
        while true
            best = best_row()
            best === nothing && return _finish_search!(
                rows, cache, "solver_failure", nothing, widenings, checkpoint_callback;
                N = N, performance_measure = performance_measure, solver = solver,
            )
            bracket_lo, bracket_hi = _neighbor_bounds(rows, Float64(best["eta_c"]))
            if bracket_hi / bracket_lo - 1 <= relative_bracket_tolerance
                return _finish_search!(
                    rows, cache, "interior", Float64(best["eta_c"]), widenings, checkpoint_callback;
                    N = N, performance_measure = performance_measure, solver = solver,
                )
            end
            evaluate_grid!(log_grid(bracket_lo, bracket_hi, num_points), "refine", refinement_round)
            if !cache_is_numerically_complete()
                return _finish_search!(
                    rows, cache, "solver_failure", nothing, widenings, checkpoint_callback;
                    N = N, performance_measure = performance_measure, solver = solver,
                )
            end
            refinement_round += 1
        end
    catch error
        if error isa TimeboxExpired
            return _finish_search!(
                rows, cache, "timebox", nothing, widenings, checkpoint_callback;
                N = N, performance_measure = performance_measure, solver = solver,
            )
        elseif error isa StrictStatusFailure
            return _finish_search!(
                rows, cache, "solver_failure", nothing, widenings, checkpoint_callback;
                N = N, performance_measure = performance_measure, solver = solver,
            )
        end
        rethrow()
    end
end

function solve_pep_point(
    N::Integer,
    performance_measure::Symbol,
    eta_c::Real;
    solver::Symbol,
    pfeas_tolerance::Real = DEFAULT_PFEAS_TOLERANCE,
    dfeas_tolerance::Real = DEFAULT_DFEAS_TOLERANCE,
)
    N >= 1 || throw(ArgumentError("N must be positive"))
    eta_c > 0 || throw(ArgumentError("eta_c must be positive"))
    L = 1.0
    eta = inv(Float64(eta_c) * L)
    alpha_alg = eta * OffsetArray(ones(N), 0:(N - 1))
    beta_alg = eta * OffsetArray(ones(N), 0:(N - 1))
    iota_x, iota_u, alpha, phi, beta, psi = feasible_stepsize_generator(
        N, alpha_alg, beta_alg; alg = :AltGDA,
    )
    return solve_primal_with_known_stepsizes(
        N,
        alpha,
        beta,
        phi,
        psi,
        measure_weights(performance_measure),
        sqrt(2.0),
        sqrt(2.0),
        1.0,
        1.0,
        L,
        1.0,
        iota_x,
        iota_u;
        show_output = :off,
        radius_constr = :on,
        diam_constr = :off,
        simplex_specific_constraints = :off,
        minimize_printing = :on,
        solver = solver,
        pfeas_tolerance = pfeas_tolerance,
        dfeas_tolerance = dfeas_tolerance,
    )
end

function _selected_payload(raw, summary)
    raw === nothing && return Dict{String,Any}()
    return Dict{String,Any}(
        "N" => summary["N"],
        "performance_measure" => summary["performance_measure"],
        "eta_c" => summary["selected_eta_c"],
        "eta" => summary["selected_eta"],
        "objective" => _raw_field(raw, :objective),
        "G_xv" => _raw_field(raw, :G_xv),
        "G_uy" => _raw_field(raw, :G_uy),
        "nu" => _raw_field(raw, :nu),
        "termination_status" => string(_raw_field(raw, :termination_status, "UNKNOWN")),
        "primal_status" => string(_raw_field(raw, :primal_status, "UNKNOWN")),
        "dual_status" => string(_raw_field(raw, :dual_status, "UNKNOWN")),
        "solve_seconds" => _raw_field(raw, :solve_seconds),
        "solver" => string(_raw_field(raw, :solver, "unknown")),
        "pfeas_tolerance" => _raw_field(raw, :pfeas_tolerance),
        "dfeas_tolerance" => _raw_field(raw, :dfeas_tolerance),
    )
end

function _checkpoint_callback(path::AbstractString, N::Integer, performance_measure::Symbol)
    return function (rows)
        save_jld_atomic(
            path;
            N = Int(N),
            performance_measure = String(performance_measure),
            updated_at = string(now()),
            curve_rows = rows,
        )
        return nothing
    end
end

function _write_and_promote_csv(name, header, rows, scratch_dir, output_dir)
    scratch_path = write_csv_atomic(joinpath(scratch_dir, name), header, rows)
    return promote_file(scratch_path, joinpath(output_dir, name))
end

function _write_and_promote_jld(name, scratch_dir, output_dir; kwargs...)
    scratch_path = save_jld_atomic(joinpath(scratch_dir, name); kwargs...)
    return promote_file(scratch_path, joinpath(output_dir, name))
end

function _run_one_search(
    N,
    performance_measure;
    solver,
    scratch_dir,
    deadline,
    abort_on_non_strict = false,
)
    haskey(ARCHIVED_ERGODIC_ETA, N) || throw(ArgumentError(
        "no archived ergodic eta is registered for N=$N; it is required by the flat-curve rule",
    ))
    checkpoint_path = joinpath(
        scratch_dir,
        "checkpoints",
        "checkpoint_$(performance_measure)_N$(N).jld",
    )
    callback = _checkpoint_callback(checkpoint_path, N, performance_measure)
    checkpoint_rows = Dict{String,Any}[]
    if isfile(checkpoint_path)
        payload = load_jld(checkpoint_path)
        all(haskey(payload, field) for field in ("N", "performance_measure", "curve_rows")) ||
            throw(ArgumentError("checkpoint rejected: required top-level metadata is missing"))
        payload_N = Int(payload["N"])
        payload_measure = Symbol(payload["performance_measure"])
        payload_N == N || throw(ArgumentError("checkpoint N does not match the requested horizon"))
        payload_measure == performance_measure || throw(ArgumentError(
            "checkpoint performance measure does not match the requested measure",
        ))
        checkpoint_rows = Dict{String,Any}[
            Dict{String,Any}(string(key) => value for (key, value) in pairs(row))
            for row in payload["curve_rows"]
        ]
        rows_valid, rows_reason = _checkpoint_rows_valid(
            checkpoint_rows;
            N = N,
            performance_measure = performance_measure,
            solver = solver,
        )
        rows_valid || throw(ArgumentError("checkpoint rejected: $rows_reason"))

        selected_rows = filter(row -> row["selected"] === true, checkpoint_rows)
        if length(selected_rows) == 1
            selected_eta_c = Float64(only(selected_rows)["eta_c"])
            eta_c_values = Float64[row["eta_c"] for row in checkpoint_rows]
            classification = if only(selected_rows)["search_phase"] == "canonical_flat"
                "flat"
            elseif isapprox(selected_eta_c, minimum(eta_c_values); rtol = 2e-13, atol = 0.0)
                "boundary_lower"
            elseif isapprox(selected_eta_c, maximum(eta_c_values); rtol = 2e-13, atol = 0.0)
                "boundary_upper"
            else
                "interior"
            end
            widen_rounds = Int[
                row["search_round"] for row in checkpoint_rows if row["search_phase"] == "widen"
            ]
            widenings = isempty(widen_rounds) ? 0 : maximum(widen_rounds)
            cache = Dict{String,Any}()
            for (row_index, row) in enumerate(checkpoint_rows)
                cache[_cache_key(Float64(row["eta_c"]))] = (
                    row_index = row_index,
                    raw = _raw_from_record(row),
                )
            end
            println("Reusing completed checkpoint for N=$N ($(performance_measure)); no SDP point is repeated.")
            return _finish_search!(
                checkpoint_rows,
                cache,
                classification,
                selected_eta_c,
                widenings,
                callback;
                N = N,
                performance_measure = performance_measure,
                solver = solver,
            )
        elseif length(selected_rows) > 1
            throw(ArgumentError("checkpoint contains more than one selected point"))
        end
        println("Resuming $(length(checkpoint_rows)) cached points for N=$N ($(performance_measure)).")
    end
    evaluator = eta_c -> solve_pep_point(
        N,
        performance_measure,
        eta_c;
        solver = solver,
        pfeas_tolerance = DEFAULT_PFEAS_TOLERANCE,
        dfeas_tolerance = DEFAULT_DFEAS_TOLERANCE,
    )
    return search_eta_c(
        evaluator;
        canonical_eta = ARCHIVED_ERGODIC_ETA[N],
        N = N,
        performance_measure = performance_measure,
        solver = solver,
        checkpoint_callback = callback,
        deadline = deadline,
        initial_rows = checkpoint_rows,
        abort_on_non_strict = abort_on_non_strict,
    )
end

function _curve_name(prefix, performance_measure, N)
    return "$(prefix)_$(performance_measure)_eta_curve_N$(N).csv"
end

function _validation_fields!(summary, reference)
    summary["validation_reference_eta"] = reference.eta
    summary["validation_reference_objective"] = reference.objective
    selected_eta = summary["selected_eta"]
    selected_objective = summary["selected_objective"]
    spacing = summary["eta_grid_spacing"]
    objective_error = selected_objective isa Real ? abs(selected_objective - reference.objective) : nothing
    eta_match = selected_eta isa Real && spacing isa Real &&
                abs(selected_eta - reference.eta) <= spacing + 16eps(Float64)
    validation_pass = summary["all_optimal"] === true &&
                      objective_error isa Real && objective_error <= 1e-2 &&
                      eta_match
    summary["validation_objective_error"] = objective_error
    summary["validation_eta_match"] = eta_match
    summary["validation_pass"] = validation_pass
    summary["decision"] = validation_pass ? "PASS" : "FAIL"
    summary["decision_reason"] = validation_pass ?
        "strict statuses, objective tolerance, and eta-grid check passed" :
        "at least one strict validation gate failed"
    return validation_pass
end

function run_validation(; solver, output_dir, scratch_dir, n_list, max_seconds)
    started = time()
    deadline = started + min(Float64(max_seconds), DEFAULT_VALIDATION_SECONDS)
    summaries = Dict{String,Any}[]
    selected_results = Dict{String,Any}()
    all_rows = Dict{String,Any}[]
    validation_ok = true

    for N in n_list
        haskey(VALIDATION_REFERENCES, N) || throw(ArgumentError("no validation reference is registered for N=$N"))
        println("Validation N=$N (:avg) ...")
        result = _run_one_search(
            N,
            :avg;
            solver = solver,
            scratch_dir = scratch_dir,
            deadline = deadline,
        )
        append!(all_rows, result.rows)
        passed = _validation_fields!(result.summary, VALIDATION_REFERENCES[N])
        push!(summaries, result.summary)
        selected_results[string(N)] = _selected_payload(result.selected_payload, result.summary)
        _write_and_promote_csv(
            _curve_name("validation", :avg, N),
            CURVE_HEADER,
            result.rows,
            scratch_dir,
            output_dir,
        )
        @printf(
            "N=%d class=%s eta=%.9g objective=%.9g solves=%d pass=%s\n",
            N,
            result.summary["classification"],
            something(result.summary["selected_eta"], NaN),
            something(result.summary["selected_objective"], NaN),
            result.summary["num_solves"],
            passed,
        )
        if !passed
            validation_ok = false
            break
        end
    end

    expected = sort(collect(keys(VALIDATION_REFERENCES)))
    complete = sort([Int(summary["N"]) for summary in summaries]) == expected
    validation_ok &= complete && solver == :mosek
    if solver != :mosek
        validation_ok = false
        for summary in summaries
            summary["decision"] = "DIAGNOSTIC_ONLY"
            summary["decision_reason"] = "Clarabel is not the authoritative validation solver"
        end
    elseif !complete && all(summary["validation_pass"] === true for summary in summaries)
        for summary in summaries
            summary["decision"] = "PARTIAL"
            summary["decision_reason"] = "the required N=5,10,30 validation set is incomplete"
        end
    end

    _write_and_promote_csv(
        "validation_avg_summary.csv",
        SUMMARY_HEADER,
        summaries,
        scratch_dir,
        output_dir,
    )
    _write_and_promote_jld(
        "AltGDA_avg_5_30.jld",
        scratch_dir,
        output_dir;
        format = "JLD2",
        finite_horizon_relaxation = true,
        generated_at = string(now()),
        curve_rows = all_rows,
        summary_rows = summaries,
        selected_results = selected_results,
    )
    println(validation_ok ? "AVERAGED VALIDATION: PASS" : "AVERAGED VALIDATION: FAIL/INCOMPLETE")
    return validation_ok
end

function _summary_gate(
    rows;
    expected_horizons,
    performance_measure,
    decision,
    require_validation_pass = false,
)
    length(rows) == length(expected_horizons) || return false, "summary row count is not exact"
    observed_horizons = try
        parse.(Int, [get(row, "N", "") for row in rows])
    catch
        return false, "summary contains an invalid horizon"
    end
    sort(observed_horizons) == sort(collect(expected_horizons)) ||
        return false, "summary horizon set is not exact"
    length(unique(observed_horizons)) == length(observed_horizons) ||
        return false, "summary contains a duplicate horizon"
    all(get(row, "performance_measure", "") == String(performance_measure) for row in rows) ||
        return false, "summary performance measure is not exact"
    all(get(row, "solver", "") == "mosek" for row in rows) ||
        return false, "summary is not authoritative MOSEK evidence"
    all(get(row, "classification", "") in PERMITTED_SEARCH_CLASSIFICATIONS for row in rows) ||
        return false, "summary contains an incomplete classification"
    all(get(row, "all_optimal", "") == "true" for row in rows) ||
        return false, "summary contains a non-strict solver result"
    all(get(row, "decision", "") == decision for row in rows) ||
        return false, "summary decision is not $decision"
    all(!isempty(get(row, "selected_eta_c", "")) &&
        !isempty(get(row, "selected_eta", "")) &&
        !isempty(get(row, "selected_objective", "")) for row in rows) ||
        return false, "summary is missing a selected point"
    if require_validation_pass
        all(get(row, "validation_pass", "") == "true" for row in rows) ||
            return false, "at least one averaged validation row failed"
    end
    return true, "summary gate passed"
end

function _curve_gate(rows; N, performance_measure)
    isempty(rows) && return false, "curve is empty"
    all(get(row, "N", "") == string(N) for row in rows) ||
        return false, "curve horizon is not exact"
    all(get(row, "performance_measure", "") == String(performance_measure) for row in rows) ||
        return false, "curve performance measure is not exact"
    all(get(row, "solver", "") == "mosek" for row in rows) ||
        return false, "curve is not authoritative MOSEK evidence"
    all(
        get(row, "termination_status", "") == "OPTIMAL" &&
        get(row, "primal_status", "") == "FEASIBLE_POINT" &&
        get(row, "dual_status", "") == "FEASIBLE_POINT"
        for row in rows
    ) || return false, "curve contains a non-strict solver status"
    objectives_available = try
        all(isfinite(parse(Float64, get(row, "objective", ""))) for row in rows)
    catch
        false
    end
    objectives_available || return false, "curve contains an unavailable objective"
    tolerances_valid = try
        all(
            _tolerance_matches(
                parse(Float64, get(row, "pfeas_tolerance", "")),
                DEFAULT_PFEAS_TOLERANCE,
            ) &&
            _tolerance_matches(
                parse(Float64, get(row, "dfeas_tolerance", "")),
                DEFAULT_DFEAS_TOLERANCE,
            )
            for row in rows
        )
    catch
        false
    end
    tolerances_valid || return false, "curve contains a noncanonical solver tolerance"
    eta_pairs = try
        [
            (
                parse(Float64, get(row, "eta_c", "")),
                parse(Float64, get(row, "eta", "")),
            )
            for row in rows
        ]
    catch
        return false, "curve contains invalid eta data"
    end
    all(
        isfinite(eta_c) && eta_c > 0 && isfinite(eta) && eta > 0 &&
        isapprox(eta, inv(eta_c); rtol = 1e-12, atol = 0.0)
        for (eta_c, eta) in eta_pairs
    ) || return false, "curve contains inconsistent eta and eta_c data"
    eta_c_keys = [_cache_key(eta_c) for (eta_c, _) in eta_pairs]
    length(eta_c_keys) == length(unique(eta_c_keys)) ||
        return false, "curve contains a duplicate eta_c"
    count(get(row, "selected", "") == "true" for row in rows) == 1 ||
        return false, "curve does not contain exactly one selected point"
    return true, "curve gate passed"
end

function _flat_csv_selection_matches(rows; N)
    haskey(ARCHIVED_ERGODIC_ETA, N) || return false
    selected_rows = filter(row -> get(row, "selected", "") == "true", rows)
    length(selected_rows) == 1 || return false
    selected_eta = try
        parse(Float64, get(only(selected_rows), "eta", ""))
    catch
        return false
    end
    return isapprox(selected_eta, ARCHIVED_ERGODIC_ETA[N]; rtol = 1e-12, atol = 0.0)
end

function _evidence_gate(
    output_dir;
    summary_name,
    curve_prefix,
    horizons,
    performance_measure,
    decision,
    require_validation_pass = false,
)
    summary_path = joinpath(output_dir, summary_name)
    isfile(summary_path) || return false, "$summary_name is missing"
    summary_rows = read_simple_csv(summary_path)
    passed, reason = _summary_gate(
        summary_rows;
        expected_horizons = horizons,
        performance_measure = performance_measure,
        decision = decision,
        require_validation_pass = require_validation_pass,
    )
    passed || return false, "$summary_name: $reason"
    summary_by_horizon = Dict(parse(Int, row["N"]) => row for row in summary_rows)
    for N in horizons
        curve_name = _curve_name(curve_prefix, performance_measure, N)
        curve_path = joinpath(output_dir, curve_name)
        isfile(curve_path) || return false, "$curve_name is missing"
        curve_rows = read_simple_csv(curve_path)
        passed, reason = _curve_gate(
            curve_rows;
            N = N,
            performance_measure = performance_measure,
        )
        passed || return false, "$curve_name: $reason"
        if summary_by_horizon[N]["classification"] == "flat"
            _flat_csv_selection_matches(curve_rows; N = N) ||
                return false, "$curve_name: flat selection is not the archived canonical eta"
        end
    end
    return true, "authoritative evidence gate passed"
end

function _authoritative_validation_passed(output_dir)
    return _evidence_gate(
        output_dir;
        summary_name = "validation_avg_summary.csv",
        curve_prefix = "validation",
        horizons = [5, 10, 30],
        performance_measure = :avg,
        decision = "PASS",
        require_validation_pass = true,
    )
end

function _authoritative_pilot_go(output_dir)
    return _evidence_gate(
        output_dir;
        summary_name = "pilot_lst_summary.csv",
        curve_prefix = "pilot",
        horizons = [5, 10, 15],
        performance_measure = :lst,
        decision = "GO",
    )
end

function _fit_runtime_model(summaries, rows)
    dimensions = Float64[]
    medians = Float64[]
    for summary in summaries
        N = Int(summary["N"])
        times = Float64[
            row["solve_seconds"] for row in rows
            if Int(row["N"]) == N && strict_status_success(row) && row["solve_seconds"] > 0
        ]
        isempty(times) && return nothing
        push!(dimensions, 2N + 11)
        push!(medians, median(times))
    end
    length(dimensions) >= 2 || return nothing
    x = log.(dimensions)
    y = log.(medians)
    denominator = sum((value - mean(x))^2 for value in x)
    denominator > eps(Float64) || return nothing
    raw_exponent = sum((x[i] - mean(x)) * (y[i] - mean(y)) for i in eachindex(x)) / denominator
    exponent = clamp(raw_exponent, 3.0, 6.0)
    scale = exp(mean(y .- exponent .* x))
    solves_per_N = median([Float64(summary["num_solves"]) for summary in summaries])
    return (exponent = exponent, scale = scale, solves_per_N = solves_per_N)
end

function _greedy_shards(Ns, fit; group_name, max_seconds = 2 * 60 * 60)
    rows = Dict{String,Any}[]
    shard_start = first(Ns)
    shard_end = shard_start - 1
    shard_seconds = 0.0
    shard_index = 1

    function predicted(N)
        per_solve = fit.scale * (2N + 11)^fit.exponent
        return 2.0 * fit.solves_per_N * per_solve
    end

    function emit!(start_N, end_N, seconds, index)
        push!(rows, Dict{String,Any}(
            "range_group" => group_name,
            "shard_index" => index,
            "start_N" => start_N,
            "end_N" => end_N,
            "predicted_seconds" => seconds,
            "predicted_hours" => seconds / 3600,
            "over_two_hours" => seconds > max_seconds,
            "fit_exponent" => fit.exponent,
            "fit_scale" => fit.scale,
            "predicted_solves_per_N" => fit.solves_per_N,
            "safety_factor" => 2.0,
            "plan_source" => "pilot_loglog",
        ))
    end

    for N in Ns
        N_seconds = predicted(N)
        if shard_end >= shard_start && shard_seconds + N_seconds > max_seconds
            emit!(shard_start, shard_end, shard_seconds, shard_index)
            shard_index += 1
            shard_start = N
            shard_end = N
            shard_seconds = N_seconds
        else
            shard_end = N
            shard_seconds += N_seconds
        end
    end
    emit!(shard_start, shard_end, shard_seconds, shard_index)
    return rows
end

function _historical_shards()
    ranges = [(5, 30)]
    rows = Dict{String,Any}[]
    group_counts = Dict("5-30" => 0)
    for (start_N, end_N) in ranges
        group = "5-30"
        group_counts[group] += 1
        push!(rows, Dict{String,Any}(
            "range_group" => group,
            "shard_index" => group_counts[group],
            "start_N" => start_N,
            "end_N" => end_N,
            "predicted_seconds" => nothing,
            "predicted_hours" => nothing,
            "over_two_hours" => nothing,
            "fit_exponent" => nothing,
            "fit_scale" => nothing,
            "predicted_solves_per_N" => nothing,
            "safety_factor" => 2.0,
            "plan_source" => "historical_fallback",
        ))
    end
    return rows
end

function build_shard_plan(summaries, rows)
    fit = _fit_runtime_model(summaries, rows)
    fit === nothing && return _historical_shards()
    return _greedy_shards(5:30, fit; group_name = "5-30")
end

function run_pilot(; solver, output_dir, scratch_dir, n_list, max_seconds)
    validated, validation_reason = _authoritative_validation_passed(output_dir)
    validated || throw(ArgumentError("pilot refused: $validation_reason"))
    solver == :mosek || throw(ArgumentError("pilot GO/NO-GO evidence must use authoritative MOSEK"))
    sort(collect(n_list)) == [5, 10, 15] || throw(ArgumentError("the S01 pilot requires exactly N=5,10,15"))

    deadline = time() + Float64(max_seconds)
    summaries = Dict{String,Any}[]
    selected_results = Dict{String,Any}()
    all_rows = Dict{String,Any}[]
    curves_complete = true

    for N in n_list
        println("Pilot N=$N (:lst) ...")
        result = _run_one_search(
            N,
            :lst;
            solver = solver,
            scratch_dir = scratch_dir,
            deadline = deadline,
        )
        append!(all_rows, result.rows)
        push!(summaries, result.summary)
        selected_results[string(N)] = _selected_payload(result.selected_payload, result.summary)
        _write_and_promote_csv(
            _curve_name("pilot", :lst, N),
            CURVE_HEADER,
            result.rows,
            scratch_dir,
            output_dir,
        )
        complete_classification = result.summary["classification"] in
            ("interior", "boundary_lower", "boundary_upper", "flat")
        curves_complete &= complete_classification
        @printf(
            "N=%d class=%s eta=%.9g objective=%.9g solves=%d strict=%s\n",
            N,
            result.summary["classification"],
            something(result.summary["selected_eta"], NaN),
            something(result.summary["selected_objective"], NaN),
            result.summary["num_solves"],
            result.summary["all_optimal"],
        )
        result.summary["all_optimal"] === true || break
        complete_classification || break
    end

    shard_rows = build_shard_plan(summaries, all_rows)
    required_horizons_complete = sort([Int(summary["N"]) for summary in summaries]) == [5, 10, 15]
    all_pilot_optimal = required_horizons_complete && all(
        summary["all_optimal"] === true for summary in summaries
    )
    concrete_shards = !isempty(shard_rows) && all(
        Int(row["start_N"]) <= Int(row["end_N"]) for row in shard_rows
    )
    go = validated && required_horizons_complete && all_pilot_optimal &&
         curves_complete && concrete_shards
    decision = go ? "GO" : "NO-GO"
    reason = go ?
        "validation passed; pilot statuses, classifications, curves, and shard plan are complete" :
        "at least one validation, status, classification, completeness, or shard-plan gate failed"
    for summary in summaries
        summary["decision"] = decision
        summary["decision_reason"] = reason
    end

    _write_and_promote_csv(
        "pilot_lst_summary.csv",
        SUMMARY_HEADER,
        summaries,
        scratch_dir,
        output_dir,
    )
    _write_and_promote_csv(
        "pilot_lst_shard_plan.csv",
        SHARD_HEADER,
        shard_rows,
        scratch_dir,
        output_dir,
    )
    _write_and_promote_jld(
        "AltGDA_lst_5_15.jld",
        scratch_dir,
        output_dir;
        format = "JLD2",
        finite_horizon_relaxation = true,
        generated_at = string(now()),
        decision = decision,
        decision_reason = reason,
        curve_rows = all_rows,
        summary_rows = summaries,
        shard_plan = shard_rows,
        selected_results = selected_results,
    )
    println("LAST-ITERATE PILOT: $decision")
    return go
end

function _sweep_horizons(n_list)
    requested = isempty(n_list) ? copy(SWEEP_HORIZONS) : collect(Int, n_list)
    requested == SWEEP_HORIZONS || throw(ArgumentError(
        "the S02 sweep requires exactly the ordered horizon list N=5:30",
    ))
    return requested
end

function _completed_sweep_result(result; N)
    summary = result.summary
    classification = summary["classification"]
    classification in PERMITTED_SEARCH_CLASSIFICATIONS ||
        return false, "N=$N has incomplete classification $classification"
    summary["all_optimal"] === true ||
        return false, "N=$N does not have strict statuses at every evaluated point"
    isempty(result.rows) && return false, "N=$N has no evaluated points"
    all(strict_status_success, result.rows) ||
        return false, "N=$N contains a non-strict curve row"
    all(row["solver"] == "mosek" for row in result.rows) ||
        return false, "N=$N contains non-authoritative solver evidence"
    all(
        _tolerance_matches(row["pfeas_tolerance"], DEFAULT_PFEAS_TOLERANCE) &&
        _tolerance_matches(row["dfeas_tolerance"], DEFAULT_DFEAS_TOLERANCE)
        for row in result.rows
    ) || return false, "N=$N contains a noncanonical solver tolerance"
    eta_c_keys = [_cache_key(Float64(row["eta_c"])) for row in result.rows]
    length(eta_c_keys) == length(unique(eta_c_keys)) ||
        return false, "N=$N contains a duplicate eta_c"
    selected_rows = filter(row -> row["selected"] === true, result.rows)
    length(selected_rows) == 1 ||
        return false, "N=$N does not contain exactly one selected point"
    summary["num_solves"] == length(result.rows) ||
        return false, "N=$N summary solve count does not match its curve"
    selected = only(selected_rows)
    summary["selected_eta_c"] isa Real ||
        return false, "N=$N summary is missing selected eta_c"
    isapprox(
        Float64(summary["selected_eta_c"]),
        Float64(selected["eta_c"]);
        rtol = 2e-13,
        atol = 0.0,
    ) || return false, "N=$N selected point disagrees with its summary"
    if classification == "flat"
        isapprox(
            Float64(summary["selected_eta"]),
            ARCHIVED_ERGODIC_ETA[N];
            rtol = 1e-12,
            atol = 0.0,
        ) || return false, "N=$N flat selection is not the archived canonical eta"
    end
    result.selected_payload === nothing &&
        return false, "N=$N selected payload is unavailable"
    return true, "N=$N completed"
end

function _persist_sweep_aggregate(
    summaries,
    all_rows,
    selected_results,
    scratch_dir,
    output_dir;
    decision,
    decision_reason,
)
    for summary in summaries
        summary["decision"] = decision
        summary["decision_reason"] = decision_reason
    end
    _write_and_promote_csv(
        "sweep_lst_summary.csv",
        SUMMARY_HEADER,
        summaries,
        scratch_dir,
        output_dir,
    )
    _write_and_promote_jld(
        "AltGDA_lst_5_30.jld",
        scratch_dir,
        output_dir;
        format = "JLD2",
        finite_horizon_relaxation = true,
        generated_at = string(now()),
        decision = decision,
        decision_reason = decision_reason,
        required_horizons = SWEEP_HORIZONS,
        curve_rows = all_rows,
        summary_rows = summaries,
        selected_results = selected_results,
    )
    return nothing
end

function _verify_sweep_artifacts(output_dir)
    try
        summary_path = joinpath(output_dir, "sweep_lst_summary.csv")
        isfile(summary_path) || return false, "sweep_lst_summary.csv is missing"
        csv_summaries = read_simple_csv(summary_path)
        passed, reason = _summary_gate(
            csv_summaries;
            expected_horizons = SWEEP_HORIZONS,
            performance_measure = :lst,
            decision = "COMPLETE",
        )
        passed || return false, "sweep summary reload failed: $reason"
        csv_summary_by_N = Dict(parse(Int, row["N"]) => row for row in csv_summaries)

        jld_path = joinpath(output_dir, "AltGDA_lst_5_30.jld")
        isfile(jld_path) || return false, "AltGDA_lst_5_30.jld is missing"
        payload = load_jld(jld_path)
        get(payload, "decision", "") == "COMPLETE" ||
            return false, "aggregate JLD decision is not COMPLETE"
        Int.(payload["required_horizons"]) == SWEEP_HORIZONS ||
            return false, "aggregate JLD required horizon list is not exact"

        jld_summaries = payload["summary_rows"]
        length(jld_summaries) == length(SWEEP_HORIZONS) ||
            return false, "aggregate JLD summary count is not exact"
        jld_summary_by_N = Dict(Int(row["N"]) => row for row in jld_summaries)
        sort(collect(keys(jld_summary_by_N))) == SWEEP_HORIZONS ||
            return false, "aggregate JLD summary horizon set is not exact"

        selected_results = payload["selected_results"]
        Set(string.(SWEEP_HORIZONS)) == Set(string.(collect(keys(selected_results)))) ||
            return false, "aggregate JLD does not have one selected-result key per horizon"
        jld_curve_rows = payload["curve_rows"]
        expected_curve_count = 0

        for N in SWEEP_HORIZONS
            curve_name = _curve_name("sweep", :lst, N)
            curve_path = joinpath(output_dir, curve_name)
            isfile(curve_path) || return false, "$curve_name is missing"
            csv_curve = read_simple_csv(curve_path)
            passed, reason = _curve_gate(csv_curve; N = N, performance_measure = :lst)
            passed || return false, "$curve_name reload failed: $reason"
            classification = csv_summary_by_N[N]["classification"]
            if classification == "flat"
                _flat_csv_selection_matches(csv_curve; N = N) ||
                    return false, "$curve_name flat selection is not canonical"
            end
            expected_curve_count += length(csv_curve)

            jld_curve = [
                row for row in jld_curve_rows
                if Int(row["N"]) == N && row["performance_measure"] == "lst"
            ]
            length(jld_curve) == length(csv_curve) ||
                return false, "$curve_name row count disagrees with the aggregate JLD"
            all(strict_status_success, jld_curve) ||
                return false, "$curve_name JLD rows contain a non-strict status"
            all(
                _tolerance_matches(row["pfeas_tolerance"], DEFAULT_PFEAS_TOLERANCE) &&
                _tolerance_matches(row["dfeas_tolerance"], DEFAULT_DFEAS_TOLERANCE)
                for row in jld_curve
            ) || return false, "$curve_name JLD rows contain noncanonical tolerances"
            csv_eta_c = Set(_cache_key(parse(Float64, row["eta_c"])) for row in csv_curve)
            jld_eta_c = Set(_cache_key(Float64(row["eta_c"])) for row in jld_curve)
            csv_eta_c == jld_eta_c ||
                return false, "$curve_name eta_c keys disagree with the aggregate JLD"
            count(row["selected"] === true for row in jld_curve) == 1 ||
                return false, "$curve_name JLD rows do not have exactly one selected point"

            csv_summary = csv_summary_by_N[N]
            jld_summary = jld_summary_by_N[N]
            Int(jld_summary["num_solves"]) == parse(Int, csv_summary["num_solves"]) == length(csv_curve) ||
                return false, "$curve_name solve count is inconsistent"
            jld_summary["classification"] == classification ||
                return false, "$curve_name classification disagrees with the aggregate JLD"
            jld_summary["decision"] == "COMPLETE" ||
                return false, "$curve_name JLD summary decision is not COMPLETE"
            selected_csv = only(filter(row -> row["selected"] == "true", csv_curve))
            selected_jld = only(filter(row -> row["selected"] === true, jld_curve))
            selected_csv_eta = parse(Float64, selected_csv["eta"])
            selected_csv_objective = parse(Float64, selected_csv["objective"])
            isapprox(
                selected_csv_eta,
                Float64(selected_jld["eta"]);
                rtol = 1e-12,
                atol = 0.0,
            ) || return false, "$curve_name selected eta is inconsistent"
            isapprox(
                selected_csv_objective,
                Float64(selected_jld["objective"]);
                rtol = 1e-12,
                atol = 0.0,
            ) || return false, "$curve_name selected objective is inconsistent"
            isapprox(
                parse(Float64, csv_summary["selected_eta"]),
                selected_csv_eta;
                rtol = 1e-12,
                atol = 0.0,
            ) || return false, "$curve_name selected eta disagrees with its summary"
            isapprox(
                parse(Float64, csv_summary["selected_objective"]),
                selected_csv_objective;
                rtol = 1e-12,
                atol = 0.0,
            ) || return false, "$curve_name selected objective disagrees with its summary"
            isapprox(
                Float64(jld_summary["selected_eta"]),
                selected_csv_eta;
                rtol = 1e-12,
                atol = 0.0,
            ) || return false, "$curve_name JLD summary selected eta is inconsistent"
            selected_payload = selected_results[string(N)]
            isapprox(
                Float64(selected_payload["eta"]),
                Float64(selected_jld["eta"]);
                rtol = 1e-12,
                atol = 0.0,
            ) || return false, "$curve_name selected-result payload is inconsistent"
            isapprox(
                Float64(selected_payload["objective"]),
                selected_csv_objective;
                rtol = 1e-12,
                atol = 0.0,
            ) || return false, "$curve_name selected-result objective is inconsistent"
        end

        length(jld_curve_rows) == expected_curve_count ||
            return false, "aggregate JLD curve count differs from concatenated curve CSVs"
        return true, "sweep CSV/JLD semantic reload passed"
    catch error
        return false, "sweep artifact reload raised: $(sprint(showerror, error))"
    end
end

function run_sweep(; solver, output_dir, scratch_dir, n_list, max_seconds)
    horizons = _sweep_horizons(n_list)
    solver == :mosek || throw(ArgumentError(
        "the S02 sweep requires authoritative MOSEK; Clarabel is diagnostic only",
    ))
    validated, validation_reason = _authoritative_validation_passed(output_dir)
    validated || throw(ArgumentError("sweep refused: $validation_reason"))
    pilot_go, pilot_reason = _authoritative_pilot_go(output_dir)
    pilot_go || throw(ArgumentError("sweep refused: $pilot_reason"))

    deadline = time() + Float64(max_seconds)
    summaries = Dict{String,Any}[]
    selected_results = Dict{String,Any}()
    all_rows = Dict{String,Any}[]

    for N in horizons
        println("Sweep N=$N (:lst) ...")
        result = _run_one_search(
            N,
            :lst;
            solver = solver,
            scratch_dir = scratch_dir,
            deadline = deadline,
            abort_on_non_strict = true,
        )
        append!(all_rows, result.rows)
        push!(summaries, result.summary)
        completed, reason = _completed_sweep_result(result; N = N)
        if completed
            selected_results[string(N)] = _selected_payload(
                result.selected_payload,
                result.summary,
            )
            _write_and_promote_csv(
                _curve_name("sweep", :lst, N),
                CURVE_HEADER,
                result.rows,
                scratch_dir,
                output_dir,
            )
            @printf(
                "N=%d class=%s eta=%.9g objective=%.9g solves=%d strict=true\n",
                N,
                result.summary["classification"],
                result.summary["selected_eta"],
                result.summary["selected_objective"],
                result.summary["num_solves"],
            )
            _persist_sweep_aggregate(
                summaries,
                all_rows,
                selected_results,
                scratch_dir,
                output_dir;
                decision = "IN_PROGRESS",
                decision_reason = "completed N=5:$N; the exact N=5:30 sweep is still running",
            )
        else
            _persist_sweep_aggregate(
                summaries,
                all_rows,
                selected_results,
                scratch_dir,
                output_dir;
                decision = "INCOMPLETE",
                decision_reason = reason,
            )
            println("LAST-ITERATE SWEEP: INCOMPLETE ($reason)")
            return false
        end
    end

    observed = [Int(summary["N"]) for summary in summaries]
    complete = observed == SWEEP_HORIZONS &&
               length(selected_results) == length(SWEEP_HORIZONS) &&
               all(summary["all_optimal"] === true for summary in summaries)
    decision = complete ? "COMPLETE" : "INCOMPLETE"
    reason = complete ?
        "all N=5:30 horizons passed the strict status, classification, and selected-point gates" :
        "the exact N=5:30 aggregate completeness gate failed"
    _persist_sweep_aggregate(
        summaries,
        all_rows,
        selected_results,
        scratch_dir,
        output_dir;
        decision = decision,
        decision_reason = reason,
    )
    if complete
        verified, verification_reason = _verify_sweep_artifacts(output_dir)
        if !verified
            _persist_sweep_aggregate(
                summaries,
                all_rows,
                selected_results,
                scratch_dir,
                output_dir;
                decision = "INCOMPLETE",
                decision_reason = verification_reason,
            )
            println("LAST-ITERATE SWEEP: INCOMPLETE ($verification_reason)")
            return false
        end
    end
    println("LAST-ITERATE SWEEP: $decision")
    return complete
end

function _parse_cli(arguments)
    options = Dict{String,String}(
        "mode" => "self-test",
        "solver" => "mosek",
        "output-dir" => joinpath(@__DIR__, "Data"),
        "scratch-dir" => joinpath(tempdir(), "iclr27_s01_pep"),
        "n-list" => "",
        "max-seconds" => string(DEFAULT_SESSION_SECONDS),
    )
    index = 1
    while index <= length(arguments)
        argument = arguments[index]
        startswith(argument, "--") || throw(ArgumentError("unexpected positional argument: $argument"))
        name = argument[3:end]
        haskey(options, name) || throw(ArgumentError("unknown option --$name"))
        index < length(arguments) || throw(ArgumentError("option --$name requires a value"))
        options[name] = arguments[index + 1]
        index += 2
    end
    mode = Symbol(options["mode"])
    mode in (:self_test, Symbol("self-test"), :validate, :pilot, :sweep) || throw(ArgumentError(
        "--mode must be self-test, validate, pilot, or sweep",
    ))
    mode == Symbol("self-test") && (mode = :self_test)
    solver = Symbol(options["solver"])
    solver in (:mosek, :clarabel) || throw(ArgumentError("--solver must be mosek or clarabel"))
    max_seconds = parse(Float64, options["max-seconds"])
    max_seconds > 0 || throw(ArgumentError("--max-seconds must be positive"))
    n_list = isempty(options["n-list"]) ? Int[] : parse.(Int, split(options["n-list"], ','))
    return (
        mode = mode,
        solver = solver,
        output_dir = abspath(options["output-dir"]),
        scratch_dir = abspath(options["scratch-dir"]),
        n_list = n_list,
        max_seconds = max_seconds,
    )
end

function main(arguments = ARGS)
    options = _parse_cli(arguments)
    mkpath(options.output_dir)
    mkpath(options.scratch_dir)
    if options.mode == :self_test
        include(joinpath(@__DIR__, "test", "runtests.jl"))
        return 0
    elseif options.mode == :validate
        n_list = isempty(options.n_list) ? [5, 10, 30] : options.n_list
        ok = run_validation(
            solver = options.solver,
            output_dir = options.output_dir,
            scratch_dir = options.scratch_dir,
            n_list = n_list,
            max_seconds = options.max_seconds,
        )
        return ok ? 0 : 2
    elseif options.mode == :pilot
        n_list = isempty(options.n_list) ? [5, 10, 15] : options.n_list
        run_pilot(
            solver = options.solver,
            output_dir = options.output_dir,
            scratch_dir = options.scratch_dir,
            n_list = n_list,
            max_seconds = options.max_seconds,
        )
        return 0
    end
    ok = run_sweep(
        solver = options.solver,
        output_dir = options.output_dir,
        scratch_dir = options.scratch_dir,
        n_list = options.n_list,
        max_seconds = options.max_seconds,
    )
    return ok ? 0 : 2
end

if abspath(PROGRAM_FILE) == @__FILE__
    exit(main())
end
