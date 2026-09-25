
using Dates
using JSON3
using JuMP
using LinearAlgebra
using MathOptInterface
using Clarabel
using Hypatia
using Loraine
using Mosek
using MosekTools
using Printf

const MOI = MathOptInterface
const DEFAULT_SOLVER = "mosek"
const CONDITIONS = (:C1, :C2, :C3)
const INCLUDED_PSD_MATRICES = join(
    ["U_$c;V_$c;Zx_$c;Zy_$c" for c in CONDITIONS],
    ";",
)

struct Selectors
    h::Int
    eta::Float64
    Nx::Int
    Ny::Int
    I2::Vector{Int}
    I1::Vector{Int}
    x::Dict{Int, Vector{Float64}}
    q::Dict{Int, Vector{Float64}}
    dx::Dict{Int, Vector{Float64}}
    y::Dict{Int, Vector{Float64}}
    p::Dict{Int, Vector{Float64}}
    dy::Dict{Int, Vector{Float64}}
    Hx0::Matrix{Float64}
    Hx1::Matrix{Float64}
    Hy0::Matrix{Float64}
    Hy1::Matrix{Float64}
    X::Matrix{Float64}
    P::Matrix{Float64}
    Y::Matrix{Float64}
    Q::Matrix{Float64}
end

function onehot(n::Int, idx::Int)
    v = zeros(Float64, n)
    v[idx] = 1.0
    return v
end

function columns(vectors)
    return reduce(hcat, vectors)
end

function odot(a, b)
    return 0.5 .* (a * b' .+ b * a')
end

function selector_data(h::Int, eta::Float64)
    h >= 0 || error("h must be nonnegative")
    eta > 0 || error("eta must be positive")

    Nx = 2h + 8
    Ny = 2h + 9
    I2 = [-1; collect(0:(h + 2))]
    I1 = [-1; collect(0:(h + 1))]

    x = Dict{Int, Vector{Float64}}()
    q = Dict{Int, Vector{Float64}}()
    dx = Dict{Int, Vector{Float64}}()
    y = Dict{Int, Vector{Float64}}()
    p = Dict{Int, Vector{Float64}}()
    dy = Dict{Int, Vector{Float64}}()

    x[-1] = onehot(Nx, 1)
    q[-1] = onehot(Nx, 2)
    x[0] = onehot(Nx, 3)
    dx[-1] = zeros(Float64, Nx)
    for i in 0:(h + 2)
        dx[i] = onehot(Nx, 4 + i)
    end
    for i in 0:(h + 1)
        q[i] = onehot(Nx, h + 7 + i)
    end
    for i in 1:(h + 2)
        x[i] = copy(x[0])
        for t in 1:i
            x[i] .-= dx[t]
        end
        for t in 0:(i - 1)
            x[i] .-= eta .* q[t]
        end
    end

    y[-1] = onehot(Ny, 1)
    p[-1] = onehot(Ny, 2)
    y[0] = onehot(Ny, 3)
    dy[-1] = zeros(Float64, Ny)
    for i in 0:(h + 2)
        dy[i] = onehot(Ny, 4 + i)
    end
    for i in 0:(h + 2)
        p[i] = onehot(Ny, h + 7 + i)
    end
    for i in 1:(h + 2)
        y[i] = copy(y[0])
        for t in 1:i
            y[i] .-= dy[t]
        end
        for t in 1:i
            y[i] .+= eta .* p[t]
        end
    end

    Hx0 = columns([x[-1], q[-1], x[0], [dx[i] for i in 0:(h + 1)]..., [q[i] for i in 0:h]...])
    Hx1 = columns([x[-1], q[-1], x[1], [dx[i] for i in 1:(h + 2)]..., [q[i] for i in 1:(h + 1)]...])
    Hy0 = columns([y[-1], p[-1], y[0], [dy[i] for i in 0:(h + 1)]..., [p[i] for i in 0:(h + 1)]...])
    Hy1 = columns([y[-1], p[-1], y[1], [dy[i] for i in 1:(h + 2)]..., [p[i] for i in 1:(h + 2)]...])

    X = columns([x[-1], [x[i] for i in 0:(h + 2)]...])
    P = columns([p[-1], [p[i] for i in 0:(h + 2)]...])
    Y = columns([y[-1], [y[i] for i in 0:(h + 1)]...])
    Q = columns([q[-1], [q[i] for i in 0:(h + 1)]...])

    selectors = Selectors(h, eta, Nx, Ny, I2, I1, x, q, dx, y, p, dy, Hx0, Hx1, Hy0, Hy1, X, P, Y, Q)
    assert_selector_dimensions(selectors)
    return selectors
end

function assert_selector_dimensions(s::Selectors)
    h = s.h
    @assert size(s.Hx0) == (s.Nx, 2h + 6)
    @assert size(s.Hx1) == (s.Nx, 2h + 6)
    @assert size(s.Hy0) == (s.Ny, 2h + 7)
    @assert size(s.Hy1) == (s.Ny, 2h + 7)
    @assert size(s.X) == (s.Nx, h + 4)
    @assert size(s.P) == (s.Ny, h + 4)
    @assert size(s.Y) == (s.Ny, h + 3)
    @assert size(s.Q) == (s.Nx, h + 3)
    for i in 0:(h + 2)
        @assert haskey(s.x, i)
        @assert haskey(s.p, i)
        @assert haskey(s.dx, i)
        @assert haskey(s.dy, i)
    end
    for i in 0:(h + 1)
        @assert haskey(s.q, i)
    end
    return true
end

function affine_matrix_zero(n::Int, m::Int)
    return [AffExpr(0.0) for _ in 1:n, _ in 1:m]
end

function normalize_solver(solver)
    solver_id = lowercase(String(solver))
    solver_id in ("mosek", "mosektools") && return "mosek"
    solver_id in ("clarabel", "clarable") && return "clarabel"
    solver_id == "hypatia" && return "hypatia"
    solver_id == "loraine" && return "loraine"
    error("unsupported solver '$solver'; expected mosek, clarabel, hypatia, or loraine")
end

function solver_optimizer(solver)
    solver_id = normalize_solver(solver)
    solver_id == "mosek" && return MosekTools.Optimizer
    solver_id == "clarabel" && return Clarabel.Optimizer
    solver_id == "hypatia" && return Hypatia.Optimizer
    solver_id == "loraine" && return Loraine.Optimizer
    error("unsupported solver '$solver'")
end

function solver_display_name(solver)
    solver_id = normalize_solver(solver)
    solver_id == "mosek" && return "MosekTools.Optimizer"
    solver_id == "clarabel" && return "Clarabel.Optimizer"
    solver_id == "hypatia" && return "Hypatia.Optimizer"
    solver_id == "loraine" && return "Loraine.Optimizer"
    error("unsupported solver '$solver'")
end

function solver_settings_metadata(solver)
    solver_id = normalize_solver(solver)
    if solver_id == "mosek"
        return Mosek.maketask() do task
            Dict{String, Any}(
                "solver_id" => "mosek",
                "MSK_DPAR_INTPNT_CO_TOL_PFEAS" => Mosek.getdouparam(task, Mosek.MSK_DPAR_INTPNT_CO_TOL_PFEAS),
                "MSK_DPAR_INTPNT_CO_TOL_DFEAS" => Mosek.getdouparam(task, Mosek.MSK_DPAR_INTPNT_CO_TOL_DFEAS),
                "MSK_DPAR_INTPNT_CO_TOL_REL_GAP" => Mosek.getdouparam(task, Mosek.MSK_DPAR_INTPNT_CO_TOL_REL_GAP),
                "MSK_DPAR_INTPNT_CO_TOL_INFEAS" => Mosek.getdouparam(task, Mosek.MSK_DPAR_INTPNT_CO_TOL_INFEAS),
                "MSK_DPAR_INTPNT_CO_TOL_MU_RED" => Mosek.getdouparam(task, Mosek.MSK_DPAR_INTPNT_CO_TOL_MU_RED),
                "MSK_IPAR_INTPNT_MAX_ITERATIONS" => Mosek.getintparam(task, Mosek.MSK_IPAR_INTPNT_MAX_ITERATIONS),
            )
        end
    end
    if solver_id == "clarabel"
        settings = Clarabel.Settings{Float64}()
        return Dict{String, Any}(
            "solver_id" => "clarabel",
            "tol_feas" => settings.tol_feas,
            "tol_gap_abs" => settings.tol_gap_abs,
            "tol_gap_rel" => settings.tol_gap_rel,
            "tol_infeas_abs" => settings.tol_infeas_abs,
            "tol_infeas_rel" => settings.tol_infeas_rel,
            "tol_ktratio" => settings.tol_ktratio,
            "max_iter" => settings.max_iter,
        )
    end
    return Dict{String, Any}(
        "solver_id" => solver_id,
        "default_settings" => true,
    )
end

function add_symmetry_constraints!(model, X)
    n = size(X, 1)
    @constraint(model, [i = 1:n, j = (i + 1):n], X[i, j] == X[j, i])
    return nothing
end

function condition_refs()
    return Dict{Symbol, Any}(condition => nothing for condition in CONDITIONS)
end

function condition_matrix_refs()
    return Dict{Symbol, Any}(condition => nothing for condition in CONDITIONS)
end

function build_condition_lhs(
    s::Selectors,
    Mx,
    My,
    U,
    V,
    mu,
    lambdax,
    lambday,
)
    lambda_pairs = [(i, j) for i in s.I2 for j in s.I2 if j != i && j != -1]

    lhs_x = -Mx
    normal_x = affine_matrix_zero(s.Nx, s.Nx)
    for (i, j) in lambda_pairs
        normal_x .+= lambdax[(i, j)] .* odot(s.dx[j], s.x[i] - s.x[j])
    end
    operator_x = affine_matrix_zero(s.Nx, s.Nx)
    for i in s.I2, j in s.I1
        operator_x .+= mu[(i, j)] .* odot(s.x[i], s.q[j])
    end
    lhs_x .+= normal_x
    lhs_x .+= operator_x
    lhs_x .-= s.X * U * s.X'
    lhs_x .+= s.Q * V * s.Q'

    lhs_y = -My
    normal_y = affine_matrix_zero(s.Ny, s.Ny)
    for (i, j) in lambda_pairs
        normal_y .+= lambday[(i, j)] .* odot(s.dy[j], s.y[i] - s.y[j])
    end
    operator_y = affine_matrix_zero(s.Ny, s.Ny)
    for i in s.I2, j in s.I1
        operator_y .+= mu[(i, j)] .* odot(s.p[i], s.y[j])
    end
    lhs_y .+= normal_y
    lhs_y .-= operator_y
    lhs_y .+= s.P * U * s.P'
    lhs_y .-= s.Y * V * s.Y'

    return lhs_x, lhs_y
end

function build_model(
    h::Int,
    eta::Float64;
    silent::Bool = true,
    solver = DEFAULT_SOLVER,
    time_limit_sec::Union{Nothing, Float64} = nothing,
)
    s = selector_data(h, eta)
    solver_id = normalize_solver(solver)
    model = Model(solver_optimizer(solver_id))
    silent && set_silent(model)
    time_limit_sec !== nothing && set_time_limit_sec(model, time_limit_sec)

    nQx = 2h + 6
    nQy = 2h + 7
    nU = h + 4
    nV = h + 3

    @variable(model, Qx[1:nQx, 1:nQx])
    @variable(model, Qy[1:nQy, 1:nQy])
    @variable(model, Sx[1:s.Nx, 1:s.Nx])
    @variable(model, Sy[1:s.Ny, 1:s.Ny])
    add_symmetry_constraints!(model, Qx)
    add_symmetry_constraints!(model, Qy)
    add_symmetry_constraints!(model, Sx)
    add_symmetry_constraints!(model, Sy)

    U = condition_refs()
    V = condition_refs()
    Zx = condition_refs()
    Zy = condition_refs()
    mu = Dict{Symbol, Dict{Tuple{Int, Int}, VariableRef}}()
    lambdax = Dict{Symbol, Dict{Tuple{Int, Int}, VariableRef}}()
    lambday = Dict{Symbol, Dict{Tuple{Int, Int}, VariableRef}}()

    lambda_pairs = [(i, j) for i in s.I2 for j in s.I2 if j != i && j != -1]
    for condition in CONDITIONS
        cname = String(condition)
        U[condition] = @variable(model, [1:nU, 1:nU], PSD, base_name = "U_$cname")
        V[condition] = @variable(model, [1:nV, 1:nV], PSD, base_name = "V_$cname")
        Zx[condition] = @variable(model, [1:s.Nx, 1:s.Nx], PSD, base_name = "Zx_$cname")
        Zy[condition] = @variable(model, [1:s.Ny, 1:s.Ny], PSD, base_name = "Zy_$cname")

        mu[condition] = Dict{Tuple{Int, Int}, VariableRef}()
        for i in s.I2, j in s.I1
            mu[condition][(i, j)] = @variable(model, base_name = "mu_$(cname)_$(i)_$(j)")
        end
        lambdax[condition] = Dict{Tuple{Int, Int}, VariableRef}()
        lambday[condition] = Dict{Tuple{Int, Int}, VariableRef}()
        for pair in lambda_pairs
            i, j = pair
            lambdax[condition][pair] = @variable(model, lower_bound = 0.0, base_name = "lambdax_$(cname)_$(i)_$(j)")
            lambday[condition][pair] = @variable(model, lower_bound = 0.0, base_name = "lambday_$(cname)_$(i)_$(j)")
        end
    end

    Qx0 = s.Hx0 * Qx * s.Hx0'
    Qx1 = s.Hx1 * Qx * s.Hx1'
    Qy0 = s.Hy0 * Qy * s.Hy0'
    Qy1 = s.Hy1 * Qy * s.Hy1'

    Mx = Dict{Symbol, Any}(
        :C1 => Qx1 .- Qx0 .+ Sx,
        :C2 => .-Qx0,
        :C3 => odot(s.q[-1], s.x[0]) .- Sx,
    )
    My = Dict{Symbol, Any}(
        :C1 => Qy1 .- Qy0 .+ Sy,
        :C2 => .-Qy0,
        :C3 => .-odot(s.p[-1], s.y[0]) .- Sy,
    )

    lhs_x = condition_matrix_refs()
    lhs_y = condition_matrix_refs()
    for condition in CONDITIONS
        lhs_x[condition], lhs_y[condition] = build_condition_lhs(
            s,
            Mx[condition],
            My[condition],
            U[condition],
            V[condition],
            mu[condition],
            lambdax[condition],
            lambday[condition],
        )
        @constraint(model, lhs_x[condition] .== Zx[condition])
        @constraint(model, lhs_y[condition] .== Zy[condition])
    end

    @objective(model, Min, 0.0)

    refs = (; Qx, Qy, Sx, Sy, U, V, Zx, Zy, mu, lambdax, lambday, lhs_x, lhs_y)
    return model, s, refs
end

function feasible_primal_status(status)
    return status == MOI.FEASIBLE_POINT || status == MOI.NEARLY_FEASIBLE_POINT
end

function matrix_min_eigen(varmat)
    mat = Symmetric(Matrix{Float64}(value.(varmat)))
    return minimum(eigvals(mat))
end

function matrix_max_eigen(varmat)
    mat = Symmetric(Matrix{Float64}(value.(varmat)))
    return maximum(eigvals(mat))
end

function max_abs_value(exprmat)
    vals = value.(exprmat)
    return maximum(abs, vals)
end

function min_lambda_value(lambdas)
    vals = Float64[]
    for condition in CONDITIONS
        append!(vals, [value(v) for v in values(lambdas[condition])])
    end
    isempty(vals) && return Inf
    return minimum(vals)
end

function acceptable_solver_status(result; strict_optimal::Bool = false)
    if strict_optimal
        return result["termination_status"] == "OPTIMAL"
    end
    return result["termination_status"] in ("OPTIMAL", "SLOW_PROGRESS", "ALMOST_OPTIMAL")
end

function max_recorded_residual(result)
    keys = [("max_abs_lmi_residual_$(condition)_x", "max_abs_lmi_residual_$(condition)_y") for condition in CONDITIONS]
    all(haskey(result, kx) && haskey(result, ky) for (kx, ky) in keys) || return nothing
    return maximum(max(result[kx], result[ky]) for (kx, ky) in keys)
end

function min_recorded_psd_eigenvalue(result)
    eigs = Float64[]
    for condition in CONDITIONS
        for name in ("U", "V", "Zx", "Zy")
            key = "min_eig_$(name)_$(condition)"
            haskey(result, key) || return nothing
            push!(eigs, result[key])
        end
    end
    return minimum(eigs)
end

function classify_threshold_result!(
    result;
    residual_tol::Float64 = 1e-6,
    eig_tol::Float64 = -1e-7,
    lambda_tol::Float64 = -1e-8,
    strict_optimal::Bool = false,
)
    solver_ok = acceptable_solver_status(result; strict_optimal)
    primal_ok = strict_optimal ?
        result["primal_status"] == "FEASIBLE_POINT" :
        result["primal_status"] in ("FEASIBLE_POINT", "NEARLY_FEASIBLE_POINT")
    max_residual = max_recorded_residual(result)
    min_eig = min_recorded_psd_eigenvalue(result)
    min_lambda = get(result, "min_lambda", nothing)
    diagnostics_available = max_residual !== nothing && min_eig !== nothing && min_lambda !== nothing
    diagnostics_ok = diagnostics_available &&
        max_residual <= residual_tol &&
        min_eig >= eig_tol &&
        min_lambda >= lambda_tol
    feasible = solver_ok && primal_ok && diagnostics_ok
    result["threshold_classification"] = feasible ? "feasible" : "infeasible_or_ambiguous"
    result["threshold_solver_ok"] = solver_ok
    result["threshold_primal_ok"] = primal_ok
    result["threshold_diagnostics_available"] = diagnostics_available
    result["threshold_max_residual"] = max_residual
    result["threshold_min_psd_eigenvalue"] = min_eig
    result["threshold_min_lambda"] = min_lambda
    result["threshold_residual_tol"] = residual_tol
    result["threshold_psd_eig_tol"] = eig_tol
    result["threshold_lambda_tol"] = lambda_tol
    result["threshold_strict_optimal"] = strict_optimal
    return feasible
end

function solve_instance(
    h::Int,
    eta::Float64;
    silent::Bool = true,
    solver = DEFAULT_SOLVER,
    strict_optimal::Bool = false,
)
    solver_id = normalize_solver(solver)
    started_at = now()
    model, selectors, refs = build_model(h, eta; silent, solver = solver_id)
    elapsed = @elapsed optimize!(model)
    term = termination_status(model)
    primal = primal_status(model)
    dual = dual_status(model)

    result = Dict{String, Any}(
        "h" => h,
        "eta" => eta,
        "termination_status" => string(term),
        "primal_status" => string(primal),
        "dual_status" => string(dual),
        "solver_id" => solver_id,
        "solver" => solver_display_name(solver_id),
        "solver_settings" => solver_settings_metadata(solver_id),
        "solve_time_seconds" => elapsed,
        "started_at" => string(started_at),
        "finished_at" => string(now()),
        "formulation" => "one_step_c123_lmi",
        "included_psd_matrices" => INCLUDED_PSD_MATRICES,
        "Nx" => selectors.Nx,
        "Ny" => selectors.Ny,
        "Qx_dim" => 2h + 6,
        "Qy_dim" => 2h + 7,
        "Sx_dim" => selectors.Nx,
        "Sy_dim" => selectors.Ny,
        "U_dim" => h + 4,
        "V_dim" => h + 3,
        "num_variables" => num_variables(model),
        "num_constraints" => num_constraints(model; count_variable_in_set_constraints = true),
    )

    if feasible_primal_status(primal)
        for condition in CONDITIONS
            result["max_abs_lmi_residual_$(condition)_x"] =
                max_abs_value(refs.lhs_x[condition] .- refs.Zx[condition])
            result["max_abs_lmi_residual_$(condition)_y"] =
                max_abs_value(refs.lhs_y[condition] .- refs.Zy[condition])
            result["min_eig_U_$(condition)"] = matrix_min_eigen(refs.U[condition])
            result["min_eig_V_$(condition)"] = matrix_min_eigen(refs.V[condition])
            result["min_eig_Zx_$(condition)"] = matrix_min_eigen(refs.Zx[condition])
            result["min_eig_Zy_$(condition)"] = matrix_min_eigen(refs.Zy[condition])
        end
        result["max_abs_lmi_residual"] = max_recorded_residual(result)
        result["min_psd_eigenvalue"] = min_recorded_psd_eigenvalue(result)
        result["min_lambda"] = min(
            min_lambda_value(refs.lambdax),
            min_lambda_value(refs.lambday),
        )
        result["lambda_min_Qx"] = matrix_min_eigen(refs.Qx)
        result["lambda_min_Qy"] = matrix_min_eigen(refs.Qy)
        result["lambda_max_Qx"] = matrix_max_eigen(refs.Qx)
        result["lambda_max_Qy"] = matrix_max_eigen(refs.Qy)
        result["sigma_plus_Qx"] = max(result["lambda_max_Qx"], 0.0)
        result["sigma_plus_Qy"] = max(result["lambda_max_Qy"], 0.0)
        classify_threshold_result!(result; strict_optimal)
        result["passed"] = result["threshold_classification"] == "feasible"
    else
        result["passed"] = false
        result["threshold_strict_optimal"] = strict_optimal
    end

    return result
end

function solve_threshold_point(
    h::Int,
    eta::Float64,
    phase::String;
    silent::Bool,
    residual_tol::Float64,
    eig_tol::Float64,
    lambda_tol::Float64,
    solver = DEFAULT_SOLVER,
    strict_optimal::Bool = false,
)
    @info "Solving C1-C2-C3 LMI threshold-search instance" h eta phase solver
    result = solve_instance(h, eta; silent, solver, strict_optimal)
    result["threshold_phase"] = phase
    classify_threshold_result!(result; residual_tol, eig_tol, lambda_tol, strict_optimal)
    result["passed"] = result["threshold_classification"] == "feasible"
    return result
end

function threshold_search_for_h(
    h::Int;
    start_eta::Float64,
    probes::Vector{Float64},
    cap::Float64,
    eta_tolerance::Float64,
    residual_tol::Float64,
    eig_tol::Float64,
    lambda_tol::Float64,
    silent::Bool,
    solver = DEFAULT_SOLVER,
    strict_optimal::Bool = false,
)
    solves = Any[]
    start = solve_threshold_point(
        h,
        start_eta,
        "start";
        silent,
        residual_tol,
        eig_tol,
        lambda_tol,
        solver,
        strict_optimal,
    )
    push!(solves, start)
    if start["threshold_classification"] != "feasible"
        return Dict{String, Any}(
            "h" => h,
            "threshold_status" => "start_not_certified_feasible",
            "certified_lower_bound" => nothing,
            "first_infeasible_or_ambiguous" => start_eta,
            "threshold_estimate" => nothing,
            "final_interval_width" => nothing,
            "safe_for_eta_interval_1_over_25_to_1_over_10" => false,
            "solves" => solves,
        )
    end

    lower = start_eta
    upper = nothing
    for eta in probes
        eta <= start_eta && continue
        eta > cap && continue
        result = solve_threshold_point(
            h,
            eta,
            "probe";
            silent,
            residual_tol,
            eig_tol,
            lambda_tol,
            solver,
            strict_optimal,
        )
        push!(solves, result)
        if result["threshold_classification"] == "feasible"
            lower = eta
        else
            upper = eta
            break
        end
    end

    if upper === nothing
        return Dict{String, Any}(
            "h" => h,
            "threshold_status" => "lower_bound_only",
            "certified_lower_bound" => lower,
            "first_infeasible_or_ambiguous" => nothing,
            "threshold_estimate" => lower,
            "final_interval_width" => nothing,
            "safe_for_eta_interval_1_over_25_to_1_over_10" => lower >= 0.1,
            "solves" => solves,
        )
    end

    while upper - lower > eta_tolerance
        eta = 0.5 * (lower + upper)
        result = solve_threshold_point(
            h,
            eta,
            "bisection";
            silent,
            residual_tol,
            eig_tol,
            lambda_tol,
            solver,
            strict_optimal,
        )
        push!(solves, result)
        if result["threshold_classification"] == "feasible"
            lower = eta
        else
            upper = eta
        end
    end

    return Dict{String, Any}(
        "h" => h,
        "threshold_status" => "bracketed",
        "certified_lower_bound" => lower,
        "first_infeasible_or_ambiguous" => upper,
        "threshold_estimate" => lower,
        "final_interval_width" => upper - lower,
        "safe_for_eta_interval_1_over_25_to_1_over_10" => lower >= 0.1,
        "solves" => solves,
    )
end

function run_threshold_search(;
    output_path::String,
    silent::Bool = true,
    solver = DEFAULT_SOLVER,
    strict_optimal::Bool = false,
)
    solver_id = normalize_solver(solver)
    start_eta = 0.04
    probes = [0.1, 0.2, 0.4, 0.8, 1.2]
    cap = 1.2
    eta_tolerance = 1e-3
    residual_tol = 1e-6
    eig_tol = -1e-7
    lambda_tol = -1e-8
    h_values = collect(2:5)

    summaries = Any[]
    for h in h_values
        push!(
            summaries,
            threshold_search_for_h(
                h;
                start_eta,
                probes,
                cap,
                eta_tolerance,
                residual_tol,
                eig_tol,
                lambda_tol,
                silent,
                solver = solver_id,
                strict_optimal,
            ),
        )
    end

    payload = Dict{String, Any}(
        "generated_at" => string(now()),
        "formulation" => "one_step_c123_lmi",
        "solver_id" => solver_id,
        "solver" => solver_display_name(solver_id),
        "solver_settings" => solver_settings_metadata(solver_id),
        "h_values" => h_values,
        "start_eta" => start_eta,
        "probe_etas" => probes,
        "eta_cap" => cap,
        "eta_tolerance" => eta_tolerance,
        "residual_tol" => residual_tol,
        "eig_tol" => eig_tol,
        "lambda_tol" => lambda_tol,
        "included_psd_matrices" => INCLUDED_PSD_MATRICES,
        "ambiguity_policy" => "treat_as_infeasible",
        "strict_optimal" => strict_optimal,
        "threshold_summaries" => summaries,
    )
    open(output_path, "w") do io
        JSON3.write(io, payload)
        write(io, "\n")
    end
    return payload
end

function run_cases(
    cases;
    output_path::String,
    silent::Bool = true,
    solver = DEFAULT_SOLVER,
    strict_optimal::Bool = false,
)
    solver_id = normalize_solver(solver)
    results = Any[]
    for (h, eta) in cases
        @info "Solving C1-C2-C3 LMI feasibility instance" h eta solver_id
        push!(results, solve_instance(h, eta; silent, solver = solver_id, strict_optimal))
    end
    payload = Dict{String, Any}(
        "generated_at" => string(now()),
        "formulation" => "one_step_c123_lmi",
        "solver_id" => solver_id,
        "solver" => solver_display_name(solver_id),
        "solver_settings" => solver_settings_metadata(solver_id),
        "included_psd_matrices" => INCLUDED_PSD_MATRICES,
        "strict_optimal" => strict_optimal,
        "results" => results,
    )
    open(output_path, "w") do io
        JSON3.write(io, payload)
        write(io, "\n")
    end
    return payload
end

function parse_output_path(args, default_path::String)
    idx = findfirst(==("--output"), args)
    idx === nothing && return default_path
    idx < length(args) || error("--output requires a path")
    return args[idx + 1]
end

function parse_int_option(args, flag::String, default::Int)
    idx = findfirst(==(flag), args)
    idx === nothing && return default
    idx < length(args) || error("$flag requires a value")
    return parse(Int, args[idx + 1])
end

function parse_float_option(args, flag::String, default::Float64)
    idx = findfirst(==(flag), args)
    idx === nothing && return default
    idx < length(args) || error("$flag requires a value")
    return parse(Float64, args[idx + 1])
end

function parse_option(args, flag::String; default = nothing)
    idx = findfirst(==(flag), args)
    idx === nothing && return default
    idx < length(args) || error("$flag requires a value")
    return args[idx + 1]
end

function usage()
    println("""
    Usage:
      julia Code/c123_lmi_feasibility.jl --smoke [--solver SOLVER] [--strict-optimal] [--output PATH] [--verbose]
      julia Code/c123_lmi_feasibility.jl --threshold-search [--solver SOLVER] [--strict-optimal] [--output PATH] [--verbose]
      julia Code/c123_lmi_feasibility.jl --single --h H --eta ETA [--solver SOLVER] [--strict-optimal] [--output PATH] [--verbose]
      julia Code/c123_lmi_feasibility.jl --check-dimensions

    Options:
      --smoke             Solve small C1-C2-C3 LMI instances at eta = 0.04 and 0.1.
      --threshold-search  Estimate certified feasible eta lower bounds for h = 2,3,4,5.
      --single            Solve one C1-C2-C3 LMI instance and write JSON diagnostics.
      --check-dimensions  Construct selectors for h = 0,1,...,8 and assert dimensions.
      --solver SOLVER      One of mosek, clarabel, hypatia, or loraine. Default: mosek.
      --strict-optimal     Classify a solve as certified only if termination_status == OPTIMAL.
      --output PATH       Write JSON diagnostics to PATH.
      --verbose           Do not silence solver output.
    """)
end

function main(args)
    if isempty(args) || "--help" in args || "-h" in args
        usage()
        return 0
    end

    silent = !("--verbose" in args)
    solver = normalize_solver(parse_option(args, "--solver"; default = DEFAULT_SOLVER))
    strict_optimal = "--strict-optimal" in args

    if "--check-dimensions" in args
        for h in 0:8
            selector_data(h, 0.1)
        end
        println("C1-C2-C3 selector dimension checks passed for h=0:8")
        return 0
    elseif "--smoke" in args
        output_path = parse_output_path(args, joinpath(@__DIR__, "c123_lmi_smoke_results.json"))
        payload = run_cases([(2, 0.04), (2, 0.1)]; output_path, silent, solver, strict_optimal)
        println("Wrote $(length(payload["results"])) smoke result(s) to $output_path")
        for result in payload["results"]
            @printf(
                "h=%d eta=%.6g status=%s primal=%s passed=%s max_residual=%s min_psd_eig=%s min_lambda=%s\n",
                result["h"],
                result["eta"],
                result["termination_status"],
                result["primal_status"],
                string(get(result, "passed", false)),
                string(get(result, "max_abs_lmi_residual", missing)),
                string(get(result, "min_psd_eigenvalue", missing)),
                string(get(result, "min_lambda", missing)),
            )
        end
        return all(get(result, "passed", false) for result in payload["results"]) ? 0 : 1
    elseif "--single" in args
        h = parse_int_option(args, "--h", 2)
        eta = parse_float_option(args, "--eta", 0.1)
        output_path = parse_output_path(args, joinpath(@__DIR__, "c123_lmi_h$(h)_eta$(replace(@sprintf("%.12g", eta), "." => "p")).json"))
        payload = run_cases([(h, eta)]; output_path, silent, solver, strict_optimal)
        result = only(payload["results"])
        @printf(
            "h=%d eta=%.6g status=%s primal=%s passed=%s max_residual=%s min_psd_eig=%s min_lambda=%s sigma_plus=(%s,%s)\n",
            result["h"],
            result["eta"],
            result["termination_status"],
            result["primal_status"],
            string(get(result, "passed", false)),
            string(get(result, "max_abs_lmi_residual", missing)),
            string(get(result, "min_psd_eigenvalue", missing)),
            string(get(result, "min_lambda", missing)),
            string(get(result, "sigma_plus_Qx", missing)),
            string(get(result, "sigma_plus_Qy", missing)),
        )
        return get(result, "passed", false) ? 0 : 1
    elseif "--threshold-search" in args
        output_path = parse_output_path(args, joinpath(@__DIR__, "c123_lmi_threshold_search_results.json"))
        payload = run_threshold_search(; output_path, silent, solver, strict_optimal)
        println("Wrote $(length(payload["threshold_summaries"])) threshold summary result(s) to $output_path")
        for summary in payload["threshold_summaries"]
            @printf(
                "h=%d status=%s lower=%s first_bad=%s safe_eta_0p04_to_0p1=%s\n",
                summary["h"],
                summary["threshold_status"],
                string(summary["certified_lower_bound"]),
                string(summary["first_infeasible_or_ambiguous"]),
                string(summary["safe_for_eta_interval_1_over_25_to_1_over_10"]),
            )
        end
        return all(summary["safe_for_eta_interval_1_over_25_to_1_over_10"] for summary in payload["threshold_summaries"]) ? 0 : 1
    end

    error("expected --smoke, --single, --threshold-search, or --check-dimensions")
end

if abspath(PROGRAM_FILE) == @__FILE__
    exit(main(ARGS))
end
