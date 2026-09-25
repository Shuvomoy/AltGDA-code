# Lyapunov-LMI code and data

This directory contains the exact manuscript-facing C1-C2-C3 implementation:

- `c123_lmi_feasibility.jl` constructs and solves the JuMP model;
- `export_c123_lmi_figure_data.jl` includes that adjacent model file and
  regenerates the three files under `Data/`;
- `Data/c123_lmi_optimal_eta_ranges.csv` and
  `Data/c123_lmi_optimal_eta_heatmap.csv` supply Figure 2; and
- `Data/c123_lmi_eta0p1_diagnostics.csv` records the representative
  `eta=0.1` diagnostics.

The reported outputs use MOSEK with termination status `OPTIMAL`, primal
status `FEASIBLE_POINT`, maximum reconstructed affine residual at most
`1e-6`, minimum recorded PSD eigenvalue at least `-1e-7`, and minimum
multiplier at least `-1e-8`. They are epsilon-feasibility diagnostics with
the stated numerical tolerances.

## Environment

`Project.toml` declares every external package imported by the unchanged
model file. No authoritative manifest was preserved for the recorded LMI
run, so `Pkg.instantiate()` resolves a compatible current environment rather
than recreating an exact historical one.

Run these commands from `Julia-code/`:

```powershell
julia --startup-file=no --project=lmi -e 'using Pkg; Pkg.instantiate()'
julia --startup-file=no --project=lmi lmi/c123_lmi_feasibility.jl --check-dimensions
julia --startup-file=no --project=lmi lmi/c123_lmi_feasibility.jl --smoke --solver mosek --strict-optimal --output <temporary-output-file>.json
julia --startup-file=no --project=lmi lmi/export_c123_lmi_figure_data.jl --output-dir <temporary-output-directory>
```

The full exporter performs many MOSEK solves and overwrites its three output
files. A fresh run is not byte-identical because it records a generation
timestamp; compare numerical fields and status/tolerance gates instead. The
dimension check constructs no optimization model and performs no solver call;
the smoke test and exporter require a working MOSEK installation and license.
