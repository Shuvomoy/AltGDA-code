
using JuMP
using LinearAlgebra
using OffsetArrays

"""
    measure_weights(performance_measure::Symbol)

Return the four objective weights `(c_avg, c_min, c_lst, c_iia)` used by the
matrix-game PEP. The ICLR 2027 experiments support the averaged gap (`:avg`)
and last-iterate gap (`:lst`) only.
"""
function measure_weights(performance_measure::Symbol)
    performance_measure == :avg && return (1, 0, 0, 0)
    performance_measure == :lst && return (0, 0, 1, 0)
    throw(ArgumentError(
        "unsupported performance measure $(repr(performance_measure)); expected :avg or :lst",
    ))
end

function e_i(n, i)
    e_i_vec = zeros(n, 1)
    e_i_vec[i] = 1
    return e_i_vec
end

nov(x) = OffsetArrays.no_offset_view(x)

function ⊙(a, b)
    return ((a * b') .+ transpose(a * b')) ./ 2
end

⊙(a) = a * transpose(a)

function fix_if_small_coefficient!(model; atol = 1e-6)
    @info "Fixing variables with coefficients below $atol in all affine constraints"
    to_check = Set(all_variables(model))

    for (F, S) in list_of_constraint_types(model)
        F == AffExpr || continue
        for ci in all_constraints(model, F, S)
            object = constraint_object(ci)
            for xi in collect(to_check)
                if abs(coefficient(object.func, xi)) >= atol
                    pop!(to_check, xi)
                end
            end
        end
    end

    for xi in to_check
        fix(xi, 0.0; force = true)
    end
    return nothing
end

function generator_function_Hxv(N, α, ϕ, ι_x; q = 1, input_type = :stepsize_constant)
    dim_𝐱 = 2 * N + 11
    dim_𝐟′ = 2 * N + 11
    dim_𝐯 = 2 * N + 11

    if input_type == :stepsize_constant
        𝐱 = OffsetArray(Matrix{Float64}(undef, dim_𝐱, N + 4), 1:dim_𝐱, -3:N)
    elseif input_type == :stepsize_variable
        𝐱 = OffsetArray(Matrix{AffExpr}(undef, dim_𝐱, N + 4), 1:dim_𝐱, -3:N)
    else
        error("Invalid input_type")
    end

    𝐟′ = OffsetArray(Matrix{Float64}(undef, dim_𝐟′, N + 4), 1:dim_𝐟′, -3:N)
    𝐯 = OffsetArray(Matrix{Float64}(undef, dim_𝐯, N + 4), 1:dim_𝐯, -3:N)

    𝐱[:, -2] = e_i(dim_𝐱, 1)
    𝐱[:, -1] = e_i(dim_𝐱, 2)
    𝐱[:, 0] = e_i(dim_𝐱, 3)
    𝐱_0 = e_i(dim_𝐱, 3)

    for i in -3:N
        𝐟′[:, i] = e_i(dim_𝐟′, 7 + i)
        𝐯[:, i] = e_i(dim_𝐯, 7 + (N + 4) + i)
    end

    for i in 1:N
        𝐱[:, i] = ι_x * 𝐱_0 -
                    sum(α[i, j] * 𝐟′[:, j] for j in 0:i) -
                    sum(ϕ[i, j] * 𝐯[:, j] for j in 0:(i - 1))
    end

    𝐱[:, -3] = sum(j^q * 𝐱[:, j] for j in 1:N) / sum(j^q for j in 1:N)
    return 𝐱, 𝐟′, 𝐯
end

function generator_function_Huy(N, β, ψ, ι_u; q = 1, input_type = :stepsize_constant)
    dim_𝐮 = 2 * N + 11
    dim_𝐡′ = 2 * N + 11
    dim_𝐲 = 2 * N + 11

    if input_type == :stepsize_constant
        𝐮 = OffsetArray(Matrix{Float64}(undef, dim_𝐮, N + 4), 1:dim_𝐮, -3:N)
    elseif input_type == :stepsize_variable
        𝐮 = OffsetArray(Matrix{AffExpr}(undef, dim_𝐮, N + 4), 1:dim_𝐮, -3:N)
    else
        error("Invalid input_type")
    end

    𝐡′ = OffsetArray(Matrix{Float64}(undef, dim_𝐡′, N + 4), 1:dim_𝐡′, -3:N)
    𝐲 = OffsetArray(Matrix{Float64}(undef, dim_𝐲, N + 4), 1:dim_𝐲, -3:N)

    𝐮[:, -2] = e_i(dim_𝐮, 1)
    𝐮[:, -1] = e_i(dim_𝐮, 2)
    𝐮[:, 0] = e_i(dim_𝐮, 3)
    𝐮_0 = e_i(dim_𝐮, 3)

    for i in -3:N
        𝐡′[:, i] = e_i(dim_𝐡′, 7 + i)
        𝐲[:, i] = e_i(dim_𝐲, 7 + (N + 4) + i)
    end

    for i in 1:N
        𝐮[:, i] = ι_u * 𝐮_0 -
                    sum(β[i, j] * 𝐡′[:, j] for j in 0:i) -
                    sum(ψ[i, j] * 𝐲[:, j] for j in 0:i)
    end

    𝐮[:, -3] = sum(j^q * 𝐮[:, j] for j in 1:N) / sum(j^q for j in 1:N)
    return 𝐮, 𝐡′, 𝐲
end

A_mat_f(i, j, 𝐟′, 𝐱) = ⊙(𝐟′[:, j], 𝐱[:, i] - 𝐱[:, j])
A_mat_h(i, j, 𝐡′, 𝐮) = ⊙(𝐡′[:, j], 𝐮[:, i] - 𝐮[:, j])
B_mat_f(i, j, 𝐱) = ⊙(𝐱[:, i] - 𝐱[:, j], 𝐱[:, i] - 𝐱[:, j])
B_mat_h(i, j, 𝐮) = ⊙(𝐮[:, i] - 𝐮[:, j], 𝐮[:, i] - 𝐮[:, j])
C_mat_f(i, j, 𝐱, 𝐯) = ⊙(𝐱[:, i], 𝐯[:, j])
C_mat_h(i, j, 𝐮, 𝐲) = ⊙(𝐲[:, i], 𝐮[:, j])
E_mat_f(i, j, 𝐱, 𝐯) = C_mat_f(i, j, 𝐱, 𝐯) - C_mat_f(j, i, 𝐱, 𝐯)
E_mat_h(i, j, 𝐮, 𝐲) = C_mat_h(i, j, 𝐮, 𝐲) - C_mat_h(j, i, 𝐮, 𝐲)
S_mat_f(i, 𝐟′, 𝐯) = ⊙(𝐟′[:, i] + 𝐯[:, i], 𝐟′[:, i] + 𝐯[:, i])
S_mat_h(i, 𝐡′, 𝐲) = ⊙(𝐡′[:, i] - 𝐲[:, i], 𝐡′[:, i] - 𝐲[:, i])
D_mat_f(i, j, 𝐱) = ⊙(𝐱[:, i], 𝐱[:, j])
D_mat_h(i, j, 𝐮) = ⊙(𝐮[:, i], 𝐮[:, j])
J_mat_f(i, 𝐟′) = ⊙(𝐟′[:, i], 𝐟′[:, i])
J_mat_h(i, 𝐡′) = ⊙(𝐡′[:, i], 𝐡′[:, i])

function feasible_stepsize_generator(N, α_alg, β_alg; alg = :AltGDA)
    ι_x_input, ι_u_input = 1, 1
    if alg == :FTRL || alg == :OFTRL
        ι_x_input, ι_u_input = 0, 0
    end

    if alg == :AltGDA
        α = OffsetArray(zeros(N, N + 1), 1:N, 0:N)
        for i in 1:N, j in 1:i
            α[i, j] = α_alg[j - 1]
        end

        β = OffsetArray(zeros(N, N + 1), 1:N, 0:N)
        for i in 1:N, j in 1:i
            β[i, j] = β_alg[j - 1]
        end

        ϕ = OffsetArray(zeros(N, N), 1:N, 0:(N - 1))
        for i in 1:N, j in 0:(i - 1)
            ϕ[i, j] = α_alg[j]
        end

        ψ = OffsetArray(zeros(N, N + 1), 1:N, 0:N)
        for i in 1:N, j in 1:i
            ψ[i, j] = -β_alg[j - 1]
        end
    elseif alg == :SimGDA
        α = OffsetArray(zeros(N, N + 1), 1:N, 0:N)
        for i in 1:N, j in 1:i
            α[i, j] = α_alg[j - 1]
        end

        β = OffsetArray(zeros(N, N + 1), 1:N, 0:N)
        for i in 1:N, j in 1:i
            β[i, j] = β_alg[j - 1]
        end

        ϕ = OffsetArray(zeros(N, N), 1:N, 0:(N - 1))
        for i in 1:N, j in 0:(i - 1)
            ϕ[i, j] = α_alg[j]
        end

        ψ = OffsetArray(zeros(N, N + 1), 1:N, 0:N)
        for i in 1:N, j in 0:(i - 1)
            ψ[i, j] = -β_alg[j]
        end
    else
        throw(ArgumentError("unsupported algorithm $(repr(alg))"))
    end

    return ι_x_input, ι_u_input, α, ϕ, β, ψ
end
