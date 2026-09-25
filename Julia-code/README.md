# AltGDA computational package

This directory is a self-contained distribution of the two computational
studies reported in the AltGDA paper:

- `lmi/` contains the C1-C2-C3 Lyapunov-LMI model, its CSV exporter, and the
  three associated MOSEK data files.
- `pep/` contains the finite-horizon last-iterate duality-gap PEP driver,
  deterministic exporter, solver-free tests, and the complete archived
  CSV/JLD2 evidence bundle.

The bundled environments, scripts, tests, and data are sufficient to inspect
the implementations and rerun the supported workflows. The PEP package reads
its averaged-gap comparison input from its bundled `Data/` directory.

## Data layout

The capitalized `lmi/Data/` and `pep/Data/` directories are computational
archives used by the scripts. Case is significant on Linux.

The PEP archive includes all validation, pilot, and `T=5:30` sweep records,
the three JLD2 aggregates (which retain their historical `.jld` suffix), the
five deterministic exports, and the bundled averaged-gap comparison input.
The LMI archive contains the two Figure 2 inputs and the `eta=0.1`
diagnostics. Generated files should not be edited by hand.

## Quick verification

Run these commands from `Julia-code/`.

```powershell
julia --startup-file=no --project=pep -e 'using Pkg; Pkg.instantiate()'
julia --startup-file=no --project=pep pep/search_stepsize_lastiterate.jl --mode self-test --solver mosek --output-dir pep/Data --scratch-dir <local-scratch-directory>
julia --startup-file=no --project=pep pep/export_lastiterate_figures.jl --output-dir <temporary-output-directory>
```

The PEP self-test and export are solver-free, although their modules load the
declared solver packages. Validation, pilot, sweep, and all LMI solves require
a working MOSEK installation and license.

The LMI environment declaration is intentionally not accompanied by a
manifest: no authoritative manifest was preserved for the recorded run. After
instantiating `lmi/Project.toml`, the lightweight structural check is:

```powershell
julia --startup-file=no --project=lmi lmi/c123_lmi_feasibility.jl --check-dimensions
```

See the component READMEs for regeneration commands, solver gates, numerical
interpretation, and the current validation status.

## Scope and provenance

The package contains no LaTeX build products, exploratory solver studies, or
historical C1-only LMI code. Regeneration should first target a temporary
directory because the LMI export embeds generation timestamps and both
exporters replace destination files.
