# Last-iterate duality-gap PEP code and data

This directory contains the finite-horizon matrix-game performance-estimation
study used in the ICLR 2027 paper. The paper proves that the SDP formulation
is tight for the modeled class at each fixed horizon. The saved values are
floating-point optima at the recorded solver tolerances; computations over
`T=5:30` do not establish an asymptotic rate.

## Contents

- `search_stepsize_lastiterate.jl` runs solver-free tests or the MOSEK-gated
  validation, pilot, and sweep workflows.
- `sdp.jl`, `utils.jl`, and `csv.jl` implement the PEP model and persistence
  layer.
- `export_lastiterate_figures.jl` strictly reloads the completed sweep and
  deterministically exports the manuscript-facing CSVs.
- `test/runtests.jl` contains 139 solver-free regression tests.
- `Data/` contains the complete validation, pilot, sweep, and export bundle,
  including the averaged-gap comparison input formerly read from outside the
  package.

The legacy metadata field `finite_horizon_relaxation=true` is retained in the
archived records for format compatibility. The paper's later tightness proof
governs the current interpretation of the finite-horizon SDP.

## Environment

`Project.toml` and `Manifest.toml` pin the environment verified for this
distribution copy: Julia 1.12.5, JuMP 1.30.0, Mosek 11.0.1, MosekTools
0.15.10, Clarabel 0.11.0, OffsetArrays 1.17.0, and JLD2 0.6.3. The recorded
MOSEK binary was 11.0.29. A MOSEK license is needed for numerical solves, but
not for the self-test or deterministic export.

Run these commands from `Julia-code/`:

```powershell
julia --startup-file=no --project=pep -e 'using Pkg; Pkg.instantiate()'
julia --startup-file=no --project=pep pep/search_stepsize_lastiterate.jl --mode self-test --solver mosek --output-dir pep/Data --scratch-dir <local-scratch-directory>
julia --startup-file=no --project=pep pep/export_lastiterate_figures.jl --output-dir <temporary-output-directory>
```

The self-test validates the complete archived `T=5:30` CSV/JLD2 bundle in
addition to synthetic corruption gates. The deterministic exporter requires
exactly 26 sweep summaries and curves (676 retained points), one selection per
horizon, the recorded MOSEK status triple
`OPTIMAL / FEASIBLE_POINT / FEASIBLE_POINT`, and primal/dual feasibility
tolerances of `1e-4`.

## Solver workflows

Use one output directory and one scratch directory for the following ordered
commands. The pilot refuses to proceed unless averaged-gap validation passes;
the sweep requires both validation and pilot gates and accepts only the exact
ordered horizon set `5,6,...,30`.

```powershell
julia --startup-file=no --project=pep pep/search_stepsize_lastiterate.jl --mode validate --solver mosek --output-dir <fresh-output-directory> --scratch-dir <local-scratch-directory> --max-seconds 9000
julia --startup-file=no --project=pep pep/search_stepsize_lastiterate.jl --mode pilot --solver mosek --output-dir <fresh-output-directory> --scratch-dir <local-scratch-directory> --max-seconds 10800
julia --startup-file=no --project=pep pep/search_stepsize_lastiterate.jl --mode sweep --solver mosek --output-dir <fresh-output-directory> --scratch-dir <local-scratch-directory> --max-seconds 10800
```

All 207 archived averaged-gap validation solves and all 676 retained
last-iterate sweep points report the required status triple. Every
last-iterate stepsize curve is numerically flat under the predeclared `1e-3`
range threshold, with selected objectives at solver scale around 2. The
exporter's fixed natural-log OLS windows are `T=5:30` and `T=15:30`.

The package-local averaged-gap inputs make these workflows self-contained.
The computational formulation and numerical gates are unchanged.
