
using JuMP
using LinearAlgebra
using OffsetArrays
using Mosek
using MosekTools
using Clarabel

if !isdefined(@__MODULE__, :generator_function_Hxv)
    include(joinpath(@__DIR__, "utils.jl"))
end

function _pep_model(
    solver::Symbol,
    pfeas_tolerance::Real,
    dfeas_tolerance::Real,
)
    pfeas_tolerance > 0 || throw(ArgumentError("pfeas_tolerance must be positive"))
    dfeas_tolerance > 0 || throw(ArgumentError("dfeas_tolerance must be positive"))

    if solver == :mosek
        model = Model(MosekTools.Optimizer)
        set_attribute(model, "MSK_DPAR_INTPNT_CO_TOL_PFEAS", Float64(pfeas_tolerance))
        set_attribute(model, "MSK_DPAR_INTPNT_CO_TOL_DFEAS", Float64(dfeas_tolerance))
        return model
    elseif solver == :clarabel
        model = Model(Clarabel.Optimizer)
        set_attribute(model, "tol_feas", Float64(min(pfeas_tolerance, dfeas_tolerance)))
        return model
    end

    throw(ArgumentError("unsupported solver $(repr(solver)); expected :mosek or :clarabel"))
end

"""
    solve_primal_with_known_stepsizes(...; solver=:mosek, ...)

Solve the fixed-stepsize finite-horizon matrix-game PEP. MOSEK is the
authoritative solver; `solver=:clarabel` is available for diagnostics.

The return value is a named tuple with fields `objective`, `G_xv`, `G_uy`,
`nu`, `termination_status`, `primal_status`, `dual_status`, `solve_seconds`,
`solver`, `pfeas_tolerance`, and `dfeas_tolerance`. The first four fields are
`nothing` when the solver returns no primal values.
"""
function solve_primal_with_known_stepsizes(
    N,
    α,
    β,
    ϕ,
    ψ,
    c,
    D_x_input,
    D_u_input,
    R_x_input,
    R_u_input,
    L,
    q_input,
    ι_x_input,
    ι_u_input;
    show_output = :on,
    radius_constr = :on,
    diam_constr = :off,
    simplex_specific_constraints = :off,
    minimize_printing = :off,
    solver = :mosek,
    pfeas_tolerance = 1e-4,
    dfeas_tolerance = 1e-4,
)
    N >= 1 || throw(ArgumentError("N must be at least 1"))
    solver isa Symbol || throw(ArgumentError("solver must be :mosek or :clarabel"))

    I_N = filter(x -> x != -1, -3:N)

    if simplex_specific_constraints == :on
        D_x, D_u, R_x, R_u = sqrt(2), sqrt(2), 1, 1
    elseif simplex_specific_constraints == :off
        D_x, D_u = D_x_input, D_u_input
        R_x, R_u = R_x_input, R_u_input
    else
        throw(ArgumentError("simplex_specific_constraints must be :on or :off"))
    end

    𝐱, 𝐟′, 𝐯 = generator_function_Hxv(
        N,
        α,
        ϕ,
        ι_x_input;
        q = q_input,
        input_type = :stepsize_constant,
    )
    𝐮, 𝐡′, 𝐲 = generator_function_Huy(
        N,
        β,
        ψ,
        ι_u_input;
        q = q_input,
        input_type = :stepsize_constant,
    )

    model = _pep_model(solver, pfeas_tolerance, dfeas_tolerance)

    dim_G_xv = 2 * N + 11
    dim_G_uy = 2 * N + 11
    @variable(model, G_xv[1:dim_G_xv, 1:dim_G_xv], PSD)
    @variable(model, G_uy[1:dim_G_uy, 1:dim_G_uy], PSD)
    @variable(model, ν)

    c_avg, c_min, c_lst, c_iia = c
    @objective(
        model,
        Max,
        c_avg * tr(G_uy * (sum(E_mat_h(i, -2, 𝐮, 𝐲) for i in 1:N) / N)) +
        c_min * ν +
        c_lst * tr(G_uy * E_mat_h(N, -2, 𝐮, 𝐲)) +
        c_iia * tr(G_uy * E_mat_h(-3, -2, 𝐮, 𝐲))
    )

    if c_min >= 1e-6
        @constraint(model, con_epigraph[i = 1:N], ν <= tr(G_uy * E_mat_h(i, -2, 𝐮, 𝐲)))
    end

    @constraint(
        model,
        con_indicator_primal[i in I_N, j in I_N, i != j],
        tr(G_xv * A_mat_f(i, j, 𝐟′, 𝐱)) <= 0
    )
    @constraint(
        model,
        con_indicator_dual[i in I_N, j in I_N, i != j],
        tr(G_uy * A_mat_h(i, j, 𝐡′, 𝐮)) <= 0
    )

    @constraint(
        model,
        con_matrix_1[i = -3:N, j = -3:N],
        tr(G_xv * C_mat_f(i, j, 𝐱, 𝐯)) -
        tr(G_uy * C_mat_h(i, j, 𝐮, 𝐲)) == 0
    )

    𝐲_nov = nov(𝐲)
    𝐱_nov = nov(𝐱)
    @constraint(
        model,
        con_matrix_2,
        -(𝐲_nov' * G_uy * 𝐲_nov) +
        (L^2 * 𝐱_nov' * G_xv * 𝐱_nov) >= 0,
        PSDCone(),
    )

    𝐯_nov = nov(𝐯)
    𝐮_nov = nov(𝐮)
    @constraint(
        model,
        con_matrix_3,
        -(𝐯_nov' * G_xv * 𝐯_nov) +
        (L^2 * 𝐮_nov' * G_uy * 𝐮_nov) in PSDCone(),
    )

    if diam_constr == :on
        minimize_printing == :off && @info "Diameter constraints are on."
        @constraint(
            model,
            con_diameter_primal[i in I_N, j in I_N, i != j],
            tr(G_xv * B_mat_f(i, j, 𝐱)) <= D_x^2
        )
        @constraint(
            model,
            con_diameter_dual[i in I_N, j in I_N, i != j],
            tr(G_uy * B_mat_h(i, j, 𝐮)) <= D_u^2
        )
    elseif diam_constr == :off
        minimize_printing == :off && @info "Diameter constraints are off."
    else
        throw(ArgumentError("diam_constr must be :on or :off"))
    end

    if radius_constr == :on
        minimize_printing == :off && @info "Radius constraints are on."
        @constraint(
            model,
            con_radius_primal[i in I_N],
            tr(G_xv * D_mat_f(i, i, 𝐱)) <= R_x^2
        )
        @constraint(
            model,
            con_radius_dual[i in I_N],
            tr(G_uy * D_mat_h(i, i, 𝐮)) <= R_u^2
        )
    elseif radius_constr == :off
        minimize_printing == :off && @info "Radius constraints are off."
    else
        throw(ArgumentError("radius_constr must be :on or :off"))
    end

    if simplex_specific_constraints == :on
        minimize_printing == :off && @info "Probability-simplex constraints are on."
        @constraint(
            model,
            con_lb_prob_simplex_dual[i in I_N, j in I_N, i != j],
            tr(G_uy * D_mat_h(i, j, 𝐮)) >= 0
        )
        @constraint(
            model,
            con_ub_prob_simplex_dual[i in I_N, j in I_N, i != j],
            tr(G_uy * D_mat_h(i, j, 𝐮)) <= 1
        )
        @constraint(
            model,
            con_lb_prob_simplex_primal[i in I_N, j in I_N, i != j],
            tr(G_xv * D_mat_f(i, j, 𝐱)) >= 0
        )
        @constraint(
            model,
            con_ub_prob_simplex_primal[i in I_N, j in I_N, i != j],
            tr(G_xv * D_mat_f(i, j, 𝐱)) <= 1
        )
        @constraint(
            model,
            con_hyperplane_dual[i in I_N],
            tr(G_uy * D_mat_h(-1, i, 𝐮)) == 1
        )
        @constraint(
            model,
            con_hyperplane_primal[i in I_N],
            tr(G_xv * D_mat_f(-1, i, 𝐱)) == 1
        )
    end

    if show_output == :off
        set_silent(model)
    elseif show_output != :on
        throw(ArgumentError("show_output must be :on or :off"))
    end

    solve_seconds = @elapsed optimize!(model)
    term_status = termination_status(model)
    prim_status = primal_status(model)
    dual_stat = dual_status(model)

    if term_status != JuMP.MOI.OPTIMAL
        @warn "PEP solve did not reach optimality" termination_status = term_status primal_status = prim_status dual_status = dual_stat
    end

    values_available = JuMP.has_values(model)
    objective = values_available ? objective_value(model) : nothing
    G_xv_value = values_available ? value.(G_xv) : nothing
    G_uy_value = values_available ? value.(G_uy) : nothing
    ν_value = values_available ? value(ν) : nothing

    if show_output == :on && objective !== nothing
        @info "PEP objective value: $objective"
    end

    return (
        objective = objective,
        G_xv = G_xv_value,
        G_uy = G_uy_value,
        nu = ν_value,
        termination_status = term_status,
        primal_status = prim_status,
        dual_status = dual_stat,
        solve_seconds = solve_seconds,
        solver = solver,
        pfeas_tolerance = Float64(pfeas_tolerance),
        dfeas_tolerance = Float64(dfeas_tolerance),
    )
end
