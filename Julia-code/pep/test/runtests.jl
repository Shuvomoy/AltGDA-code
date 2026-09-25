
using Test

if !isdefined(@__MODULE__, :search_eta_c)
    include(joinpath(@__DIR__, "..", "search_stepsize_lastiterate.jl"))
end

if !isdefined(@__MODULE__, :export_lastiterate_figures)
    include(joinpath(@__DIR__, "..", "export_lastiterate_figures.jl"))
end

function successful_result(objective; solve_seconds = 0.0, solver = "synthetic")
    return (
        objective = Float64(objective),
        G_xv = nothing,
        G_uy = nothing,
        nu = nothing,
        termination_status = "OPTIMAL",
        primal_status = "FEASIBLE_POINT",
        dual_status = "FEASIBLE_POINT",
        solve_seconds = Float64(solve_seconds),
        solver = solver,
        pfeas_tolerance = 1e-4,
        dfeas_tolerance = 1e-4,
    )
end

@testset "ICLR27-S04 solver-free export and fits" begin
    data_dir = joinpath(@__DIR__, "..", "Data")
    sweep_summary = joinpath(data_dir, "sweep_lst_summary.csv")
    sweep_jld = joinpath(data_dir, "AltGDA_lst_5_30.jld")
    ergodic_csv = joinpath(data_dir, "pep_optimized_stepsizes_altgda.csv")

    @testset "predeclared fit windows" begin
        @test S04_HORIZONS == collect(5:30)
        @test S04_FULL_WINDOW == (name = "full_5_30", T_min = 5, T_max = 30)
        @test S04_TAIL_WINDOW == (name = "tail_15_30", T_min = 15, T_max = 30)
        @test length(5:30) == 26
        @test length(15:30) == 16
    end

    @testset "log-log OLS" begin
        horizons = collect(5:30)
        power_fit = fit_loglog(horizons, 3.25 .* Float64.(horizons) .^ (-1.5))
        @test power_fit.slope ≈ -1.5 atol = 2e-14
        @test power_fit.intercept ≈ log(3.25) atol = 2e-14
        @test power_fit.prefactor ≈ 3.25 atol = 2e-14
        @test power_fit.r_squared ≈ 1.0 atol = 2e-14
        @test power_fit.rmse_log < 2e-14

        constant_fit = fit_loglog(horizons, fill(2.0, length(horizons)))
        @test abs(constant_fit.slope) < 1e-14
        @test constant_fit.intercept ≈ log(2.0) atol = 2e-14
        @test constant_fit.r_squared === nothing
        @test_throws ArgumentError fit_loglog([5, 6], [1.0, 0.0])
        @test_throws ArgumentError fit_loglog([5, 5, 5], [1.0, 2.0, 3.0])
    end

    @testset "corrupt-input gates" begin
        summary_rows = read_simple_csv(sweep_summary)
        curve_rows = read_simple_csv(joinpath(data_dir, "sweep_lst_eta_curve_N5.csv"))
        @test isnothing(_s04_validate_summary_rows(summary_rows))
        @test _s04_validate_curve_rows(curve_rows, 5, summary_rows[1])["selected"] == "true"
        @test_throws ArgumentError _s04_validate_summary_rows(summary_rows[1:end-1])

        bad_status = deepcopy(curve_rows)
        bad_status[1]["termination_status"] = "ALMOST_OPTIMAL"
        @test_throws ArgumentError _s04_validate_curve_rows(bad_status, 5, summary_rows[1])

        bad_tolerance = deepcopy(curve_rows)
        bad_tolerance[1]["pfeas_tolerance"] = "1e-3"
        @test_throws ArgumentError _s04_validate_curve_rows(bad_tolerance, 5, summary_rows[1])

        duplicate_selection = deepcopy(curve_rows)
        duplicate_selection[1]["selected"] = "true"
        @test_throws ArgumentError _s04_validate_curve_rows(duplicate_selection, 5, summary_rows[1])

        duplicate_eta = deepcopy(curve_rows)
        duplicate_eta[2]["eta_c"] = duplicate_eta[1]["eta_c"]
        duplicate_eta[2]["eta"] = duplicate_eta[1]["eta"]
        @test_throws ArgumentError _s04_validate_curve_rows(duplicate_eta, 5, summary_rows[1])

        nonflat_objective = deepcopy(curve_rows)
        nonflat_objective[1]["objective"] = "99.0"
        @test_throws ArgumentError _s04_validate_curve_rows(nonflat_objective, 5, summary_rows[1])

        wrong_grid = deepcopy(curve_rows)
        wrong_grid[1]["eta_c"] = "0.51"
        wrong_grid[1]["eta"] = string(inv(0.51))
        @test_throws ArgumentError _s04_validate_curve_rows(wrong_grid, 5, summary_rows[1])

        wrong_round = deepcopy(curve_rows)
        wrong_round[1]["search_round"] = "1"
        @test_throws ArgumentError _s04_validate_curve_rows(wrong_round, 5, summary_rows[1])

        @test _s04_requires_narrative_decision(-1.0)
        @test !_s04_requires_narrative_decision(0.0)
    end

    @testset "authoritative bundle export and round trip" begin
        mktempdir() do output_dir
            outputs = export_lastiterate_figures(
                sweep_summary = sweep_summary,
                curve_dir = data_dir,
                sweep_jld = sweep_jld,
                ergodic_csv = ergodic_csv,
                output_dir = output_dir,
            )
            filenames = [spec[1] for spec in _s04_output_specs(outputs)]
            @test length(filenames) == 5
            @test all(isfile(joinpath(output_dir, filename)) for filename in filenames)
            @test _s04_header(joinpath(output_dir, "pep_lastiterate_optimized_stepsizes_altgda.csv")) == S04_PEP_EXPORT_HEADER
            @test length(read_simple_csv(joinpath(output_dir, "pep_lastiterate_optimized_stepsizes_altgda.csv"))) == 26
            @test length(read_simple_csv(joinpath(output_dir, "pep_ergodic_lastiterate_loglog_fit_points.csv"))) == 84
            @test isnothing(_s04_validate_output_bundle(output_dir, outputs))

            fit_lookup = Dict((row.series, row.window) => row for row in outputs.fit_summaries)
            @test fit_lookup[("ergodic_average", "full_5_30")].slope ≈ -0.882032959705401 atol = 2e-13
            @test fit_lookup[("ergodic_average", "tail_15_30")].slope ≈ -0.9112375274923162 atol = 2e-13
            @test abs(fit_lookup[("last_iterate", "full_5_30")].slope) < 2e-8
            @test abs(fit_lookup[("last_iterate", "tail_15_30")].slope) < 2e-8
            @test abs(fit_lookup[("last_iterate", "tail_15_30")].slope + 1) > S04_NEAR_MINUS_ONE_TOLERANCE

            gap_rows = read_simple_csv(joinpath(output_dir, "pep_ergodic_lastiterate_gap_figure_data.csv"))
            @test maximum(
                _s04_parse_int(row, "T", "test") * _s04_parse_float(row, "guide_T_minus_1", "test")
                for row in gap_rows
            ) - minimum(
                _s04_parse_int(row, "T", "test") * _s04_parse_float(row, "guide_T_minus_1", "test")
                for row in gap_rows
            ) < 1e-12
            @test maximum(
                sqrt(_s04_parse_int(row, "T", "test")) * _s04_parse_float(row, "guide_T_minus_half", "test")
                for row in gap_rows
            ) - minimum(
                sqrt(_s04_parse_int(row, "T", "test")) * _s04_parse_float(row, "guide_T_minus_half", "test")
                for row in gap_rows
            ) < 1e-12

            first_hashes = Dict(filename => _sha256_file(joinpath(output_dir, filename)) for filename in filenames)
            export_lastiterate_figures(
                sweep_summary = sweep_summary,
                curve_dir = data_dir,
                sweep_jld = sweep_jld,
                ergodic_csv = ergodic_csv,
                output_dir = output_dir,
            )
            second_hashes = Dict(filename => _sha256_file(joinpath(output_dir, filename)) for filename in filenames)
            @test first_hashes == second_hashes
        end
    end

    @testset "CLI contract" begin
        options = _s04_parse_cli(String[])
        @test options.output_dir == abspath(data_dir)
        @test options.ergodic_csv == abspath(ergodic_csv)
        @test_throws ArgumentError _s04_parse_cli(["--solver", "mosek"])
        @test_throws ArgumentError _s04_parse_cli(["positional"])
    end
end

function non_strict_result(objective)
    return (
        objective = Float64(objective),
        G_xv = nothing,
        G_uy = nothing,
        nu = nothing,
        termination_status = "ALMOST_OPTIMAL",
        primal_status = "NEARLY_FEASIBLE_POINT",
        dual_status = "NEARLY_FEASIBLE_POINT",
        solve_seconds = 0.0,
        solver = "mosek",
        pfeas_tolerance = 1e-4,
        dfeas_tolerance = 1e-4,
    )
end

@testset "ICLR27-S01/S02 last-iterate PEP port" begin
    @testset "performance-measure contract" begin
        @test measure_weights(:avg) == (1, 0, 0, 0)
        @test measure_weights(:lst) == (0, 0, 1, 0)
        @test_throws ArgumentError measure_weights(:min)
        @test_throws ArgumentError measure_weights(:last)
    end

    @testset "log-grid endpoints" begin
        grid = log_grid(0.5, 64.0, 25)
        @test length(grid) == 25
        @test first(grid) === 0.5
        @test last(grid) === 64.0
        @test issorted(grid)
        @test all(diff(log.(grid)) .> 0)
        @test maximum(abs.(diff(log.(grid)) .- first(diff(log.(grid))))) < 1e-12
        @test_throws ArgumentError log_grid(0.0, 1.0, 5)
        @test_throws ArgumentError log_grid(2.0, 1.0, 5)
        @test_throws ArgumentError log_grid(1.0, 2.0, 1)
    end

    @testset "cached interior refinement" begin
        calls = Ref(0)
        evaluator(eta_c) = begin
            calls[] += 1
            successful_result(log(eta_c / 2.0)^2)
        end
        result = search_eta_c(
            evaluator;
            canonical_eta = 0.5,
            N = 7,
            performance_measure = :lst,
            solver = :mosek,
            initial_lo = 0.5,
            initial_hi = 8.0,
            num_points = 5,
            flat_tolerance = 1e-12,
            relative_bracket_tolerance = 1e-2,
        )

        @test result.summary["classification"] == "interior"
        @test result.summary["selected_eta_c"] ≈ 2.0 rtol = 1e-12
        @test result.summary["selected_eta"] ≈ 0.5 rtol = 1e-12
        @test result.summary["final_eta_c_hi"] / result.summary["final_eta_c_lo"] - 1 <= 1e-2
        @test calls[] == result.summary["num_solves"] == length(result.rows)

        keys = [_cache_key(row["eta_c"]) for row in result.rows]
        @test length(keys) == length(unique(keys))

        refinement_rounds = [row["search_round"] for row in result.rows if row["search_phase"] == "refine"]
        @test !isempty(refinement_rounds)
        @test calls[] < 5 * (1 + maximum(refinement_rounds))
        @test count(row -> row["selected"], result.rows) == 1
        @test result.summary["all_optimal"]

        resumed_calls = Ref(0)
        resumed = search_eta_c(
            eta_c -> begin
                resumed_calls[] += 1
                successful_result(log(eta_c / 2.0)^2)
            end;
            canonical_eta = 0.5,
            N = 7,
            performance_measure = :lst,
            solver = :mosek,
            initial_lo = 0.5,
            initial_hi = 8.0,
            num_points = 5,
            flat_tolerance = 1e-12,
            relative_bracket_tolerance = 1e-2,
            initial_rows = result.rows,
        )
        @test resumed_calls[] == 0
        @test resumed.summary["classification"] == "interior"
        @test resumed.summary["selected_eta_c"] ≈ 2.0 rtol = 1e-12
    end

    @testset "capped lower boundary" begin
        result = search_eta_c(
            eta_c -> successful_result(eta_c);
            canonical_eta = 1.0,
            initial_lo = 0.5,
            initial_hi = 2.0,
            num_points = 5,
            flat_tolerance = 1e-12,
            max_widenings = 2,
        )

        @test result.summary["classification"] == "boundary_lower"
        @test result.summary["boundary_widenings"] == 2
        @test result.summary["selected_eta_c"] ≈ 0.5 / 4^2
        @test result.summary["selected_eta"] ≈ 4^2 / 0.5
        @test count(row -> row["selected"], result.rows) == 1
    end

    @testset "capped upper boundary" begin
        result = search_eta_c(
            eta_c -> successful_result(-eta_c);
            canonical_eta = 1.0,
            initial_lo = 0.5,
            initial_hi = 2.0,
            num_points = 5,
            flat_tolerance = 1e-12,
            max_widenings = 2,
        )

        @test result.summary["classification"] == "boundary_upper"
        @test result.summary["boundary_widenings"] == 2
        @test result.summary["selected_eta_c"] ≈ 2.0 * 4^2
        @test result.summary["selected_eta"] ≈ 1 / (2.0 * 4^2)
        @test count(row -> row["selected"], result.rows) == 1
    end

    @testset "flat curve uses canonical eta" begin
        calls = Float64[]
        canonical_eta = 0.8
        canonical_eta_c = inv(canonical_eta)
        result = search_eta_c(
            eta_c -> begin
                push!(calls, eta_c)
                successful_result(3.0)
            end;
            canonical_eta = canonical_eta,
            N = 5,
            performance_measure = :avg,
            initial_lo = 0.5,
            initial_hi = 8.0,
            num_points = 5,
            flat_tolerance = 1e-3,
        )

        @test result.summary["classification"] == "flat"
        @test result.summary["selected_eta_c"] ≈ canonical_eta_c
        @test result.summary["selected_eta"] ≈ canonical_eta
        @test result.summary["selected_objective"] == 3.0
        @test count(eta_c -> isapprox(eta_c, canonical_eta_c; rtol = 1e-13), calls) == 1
        selected_rows = filter(row -> row["selected"], result.rows)
        @test length(selected_rows) == 1
        @test only(selected_rows)["search_phase"] == "canonical_flat"
        @test length(result.rows) == 6
    end

    @testset "S02 scope and canonical stepsizes" begin
        @test sort(collect(keys(ARCHIVED_ERGODIC_ETA))) == SWEEP_HORIZONS
        @test ARCHIVED_ERGODIC_ETA[5] == 1.5269322725172283
        @test ARCHIVED_ERGODIC_ETA[17] == 1.4384404277467588
        @test ARCHIVED_ERGODIC_ETA[30] == 1.2493835278645404
        @test _sweep_horizons(Int[]) == collect(5:30)
        @test _sweep_horizons(collect(5:30)) == collect(5:30)
        @test_throws ArgumentError _sweep_horizons(collect(5:29))
        @test_throws ArgumentError _sweep_horizons(reverse(collect(5:30)))
        @test_throws ArgumentError _sweep_horizons(collect(6:31))

        defaults = _parse_cli(["--mode", "sweep"])
        @test defaults.mode == :sweep
        @test defaults.solver == :mosek
        @test isempty(defaults.n_list)
        explicit = _parse_cli([
            "--mode", "sweep",
            "--n-list", join(5:30, ','),
        ])
        @test explicit.n_list == collect(5:30)
        @test_throws ArgumentError _parse_cli(["--mode", "sweep-repair"])
    end

    @testset "S02 evidence-gate parsing" begin
        function summary_row(N; measure = "lst", solver = "mosek", decision = "GO",
                             classification = "flat", all_optimal = "true",
                             validation_pass = "")
            return Dict(
                "N" => string(N),
                "performance_measure" => measure,
                "solver" => solver,
                "classification" => classification,
                "all_optimal" => all_optimal,
                "decision" => decision,
                "selected_eta_c" => "0.75",
                "selected_eta" => "1.3333333333333333",
                "selected_objective" => "2.0",
                "validation_pass" => validation_pass,
            )
        end

        pilot_rows = [summary_row(N) for N in (5, 10, 15)]
        @test _summary_gate(
            pilot_rows;
            expected_horizons = [5, 10, 15],
            performance_measure = :lst,
            decision = "GO",
        )[1]
        duplicate_rows = [summary_row(5), summary_row(5), summary_row(15)]
        @test !_summary_gate(
            duplicate_rows;
            expected_horizons = [5, 10, 15],
            performance_measure = :lst,
            decision = "GO",
        )[1]
        wrong_solver_rows = deepcopy(pilot_rows)
        wrong_solver_rows[2]["solver"] = "clarabel"
        @test !_summary_gate(
            wrong_solver_rows;
            expected_horizons = [5, 10, 15],
            performance_measure = :lst,
            decision = "GO",
        )[1]

        validation_rows = [
            summary_row(N; measure = "avg", decision = "PASS", validation_pass = "true")
            for N in (5, 10, 30)
        ]
        @test _summary_gate(
            validation_rows;
            expected_horizons = [5, 10, 30],
            performance_measure = :avg,
            decision = "PASS",
            require_validation_pass = true,
        )[1]
        validation_rows[3]["validation_pass"] = "false"
        @test !_summary_gate(
            validation_rows;
            expected_horizons = [5, 10, 30],
            performance_measure = :avg,
            decision = "PASS",
            require_validation_pass = true,
        )[1]

        curve_rows = [
            Dict(
                "N" => "5",
                "performance_measure" => "lst",
                "search_phase" => selected == "true" ? "canonical_flat" : "coarse",
                "search_round" => "0",
                "eta_c" => string(0.5 + index / 10),
                "eta" => string(inv(0.5 + index / 10)),
                "solver" => "mosek",
                "termination_status" => "OPTIMAL",
                "primal_status" => "FEASIBLE_POINT",
                "dual_status" => "FEASIBLE_POINT",
                "objective" => "2.0",
                "pfeas_tolerance" => "0.0001",
                "dfeas_tolerance" => "0.0001",
                "solve_seconds" => "0.1",
                "selected" => selected,
            )
            for (index, selected) in enumerate(("false", "true", "false"))
        ]
        @test _curve_gate(curve_rows; N = 5, performance_measure = :lst)[1]
        curve_rows[1]["selected"] = "true"
        @test !_curve_gate(curve_rows; N = 5, performance_measure = :lst)[1]
        curve_rows[1]["selected"] = "false"
        curve_rows[1]["termination_status"] = "ALMOST_OPTIMAL"
        @test !_curve_gate(curve_rows; N = 5, performance_measure = :lst)[1]
        curve_rows[1]["termination_status"] = "OPTIMAL"
        curve_rows[1]["pfeas_tolerance"] = "1e-8"
        @test !_curve_gate(curve_rows; N = 5, performance_measure = :lst)[1]
        curve_rows[1]["pfeas_tolerance"] = "1e-4"
        curve_rows[1]["eta_c"] = curve_rows[2]["eta_c"]
        @test !_curve_gate(curve_rows; N = 5, performance_measure = :lst)[1]

        canonical_curve = deepcopy(curve_rows[2:2])
        canonical_curve[1]["eta"] = string(ARCHIVED_ERGODIC_ETA[5])
        canonical_curve[1]["eta_c"] = string(inv(ARCHIVED_ERGODIC_ETA[5]))
        @test _flat_csv_selection_matches(canonical_curve; N = 5)
        canonical_curve[1]["eta"] = "1.0"
        @test !_flat_csv_selection_matches(canonical_curve; N = 5)
    end

    @testset "S02 checkpoint semantic validation" begin
        N = 8
        eta_c = 2.0
        row = Dict{String,Any}(
            "N" => N,
            "performance_measure" => "lst",
            "search_phase" => "coarse",
            "search_round" => 0,
            "eta_c" => eta_c,
            "eta" => inv(eta_c),
            "objective" => 2.0,
            "termination_status" => "OPTIMAL",
            "primal_status" => "FEASIBLE_POINT",
            "dual_status" => "FEASIBLE_POINT",
            "solver" => "mosek",
            "pfeas_tolerance" => 1e-4,
            "dfeas_tolerance" => 1e-4,
            "solve_seconds" => 0.1,
            "selected" => false,
        )
        @test _checkpoint_rows_valid(
            [row]; N = N, performance_measure = :lst, solver = :mosek,
        )[1]
        wrong_N = deepcopy(row)
        wrong_N["N"] = 9
        @test !_checkpoint_rows_valid(
            [wrong_N]; N = N, performance_measure = :lst, solver = :mosek,
        )[1]
        wrong_measure = deepcopy(row)
        wrong_measure["performance_measure"] = "avg"
        @test !_checkpoint_rows_valid(
            [wrong_measure]; N = N, performance_measure = :lst, solver = :mosek,
        )[1]
        wrong_tolerance = deepcopy(row)
        wrong_tolerance["dfeas_tolerance"] = 1e-8
        @test !_checkpoint_rows_valid(
            [wrong_tolerance]; N = N, performance_measure = :lst, solver = :mosek,
        )[1]
        @test !_checkpoint_rows_valid(
            [row, deepcopy(row)]; N = N, performance_measure = :lst, solver = :mosek,
        )[1]
        missing_status = deepcopy(row)
        delete!(missing_status, "termination_status")
        @test !_checkpoint_rows_valid(
            [missing_status]; N = N, performance_measure = :lst, solver = :mosek,
        )[1]
    end

    @testset "S02 stops at first non-strict synthetic result" begin
        calls = Ref(0)
        result = search_eta_c(
            eta_c -> begin
                calls[] += 1
                non_strict_result(eta_c)
            end;
            canonical_eta = 1.0,
            N = 5,
            performance_measure = :lst,
            solver = :mosek,
            initial_lo = 0.5,
            initial_hi = 2.0,
            num_points = 5,
            abort_on_non_strict = true,
        )
        @test calls[] == 1
        @test length(result.rows) == 1
        @test result.summary["classification"] == "solver_failure"
        @test result.summary["all_optimal"] === false
        @test count(row -> row["selected"], result.rows) == 0
    end

    @testset "S02 synthetic timebox stop" begin
        calls = Ref(0)
        result = search_eta_c(
            eta_c -> begin
                calls[] += 1
                successful_result(eta_c; solver = "mosek")
            end;
            canonical_eta = 1.0,
            N = 5,
            performance_measure = :lst,
            solver = :mosek,
            deadline = time() - 1,
            abort_on_non_strict = true,
        )
        @test calls[] == 0
        @test isempty(result.rows)
        @test result.summary["classification"] == "timebox"
        @test result.summary["all_optimal"] === false
    end

    @testset "S02 aggregate semantic reload" begin
        mktempdir() do directory
            scratch_dir = joinpath(directory, "scratch")
            output_dir = joinpath(directory, "output")
            summaries = Dict{String,Any}[]
            all_rows = Dict{String,Any}[]
            selected_results = Dict{String,Any}()

            for N in SWEEP_HORIZONS
                eta = ARCHIVED_ERGODIC_ETA[N]
                eta_c = inv(eta)
                row = Dict{String,Any}(
                    "N" => N,
                    "performance_measure" => "lst",
                    "search_phase" => "canonical_flat",
                    "search_round" => 0,
                    "eta_c" => eta_c,
                    "eta" => eta,
                    "objective" => 2.0,
                    "termination_status" => "OPTIMAL",
                    "primal_status" => "FEASIBLE_POINT",
                    "dual_status" => "FEASIBLE_POINT",
                    "solver" => "mosek",
                    "pfeas_tolerance" => 1e-4,
                    "dfeas_tolerance" => 1e-4,
                    "solve_seconds" => 0.1,
                    "selected" => true,
                )
                summary = Dict{String,Any}(field => nothing for field in SUMMARY_HEADER)
                merge!(summary, Dict{String,Any}(
                    "N" => N,
                    "performance_measure" => "lst",
                    "solver" => "mosek",
                    "classification" => "flat",
                    "selected_eta_c" => eta_c,
                    "selected_eta" => eta,
                    "selected_objective" => 2.0,
                    "all_optimal" => true,
                    "num_solves" => 1,
                    "total_solve_seconds" => 0.1,
                    "final_eta_c_lo" => eta_c,
                    "final_eta_c_hi" => eta_c,
                    "boundary_widenings" => 0,
                    "eta_grid_spacing" => 0.0,
                ))
                push!(summaries, summary)
                push!(all_rows, row)
                selected_results[string(N)] = Dict{String,Any}(
                    "N" => N,
                    "eta_c" => eta_c,
                    "eta" => eta,
                    "objective" => 2.0,
                )
                _write_and_promote_csv(
                    _curve_name("sweep", :lst, N),
                    CURVE_HEADER,
                    [row],
                    scratch_dir,
                    output_dir,
                )
            end
            _persist_sweep_aggregate(
                summaries,
                all_rows,
                selected_results,
                scratch_dir,
                output_dir;
                decision = "COMPLETE",
                decision_reason = "synthetic semantic reload fixture",
            )
            verified, reason = _verify_sweep_artifacts(output_dir)
            @test verified
            @test reason == "sweep CSV/JLD semantic reload passed"

            corrupt_summary = read_simple_csv(joinpath(output_dir, "sweep_lst_summary.csv"))
            corrupt_summary[1]["decision"] = "INCOMPLETE"
            write_csv_atomic(
                joinpath(output_dir, "sweep_lst_summary.csv"),
                SUMMARY_HEADER,
                corrupt_summary,
            )
            @test !_verify_sweep_artifacts(output_dir)[1]
        end
    end

    @testset "CSV and JLD2 round trips" begin
        mktempdir() do directory
            csv_path = joinpath(directory, "roundtrip.csv")
            header = ["name", "note", "value"]
            rows = [
                (name = "plain", note = "comma, quote \" and\nnewline", value = 1.25),
                Dict("name" => "blank", "note" => nothing, "value" => -2),
            ]
            returned_csv_path = write_csv_atomic(csv_path, header, rows)
            @test returned_csv_path == abspath(csv_path)
            loaded_rows = read_simple_csv(csv_path)
            @test loaded_rows == [
                Dict("name" => "plain", "note" => "comma, quote \" and\nnewline", "value" => "1.25"),
                Dict("name" => "blank", "note" => "", "value" => "-2"),
            ]

            jld_path = joinpath(directory, "roundtrip.jld")
            returned_jld_path = save_jld_atomic(
                jld_path;
                vector = [1.0, 2.0, 3.0],
                metadata = Dict("measure" => "lst", "N" => 5),
            )
            @test returned_jld_path == abspath(jld_path)
            payload = load_jld(jld_path)
            @test payload["vector"] == [1.0, 2.0, 3.0]
            @test payload["metadata"] == Dict("measure" => "lst", "N" => 5)
            @test_throws ArgumentError save_jld_atomic(joinpath(directory, "wrong.jld2"); x = 1)
        end
    end
end
