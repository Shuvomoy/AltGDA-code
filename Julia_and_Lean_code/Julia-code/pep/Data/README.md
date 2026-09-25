# ICLR 2027 PEP Data

This directory contains the completed S01 and S02 finite-horizon matrix-game
PEP artifacts. Every numerical value is a floating-point optimum of the
audited SDP at the recorded solver tolerances. The paper proves that this
finite-horizon formulation is tight for its modeled class; the finite range
of computed horizons does not establish an asymptotic rate.

## Averaged-gap validation

The MOSEK validation used `MSK_DPAR_INTPNT_CO_TOL_PFEAS = 1e-4` and
`MSK_DPAR_INTPNT_CO_TOL_DFEAS = 1e-4`. All 207 distinct stepsize solves had
status `OPTIMAL / FEASIBLE_POINT / FEASIBLE_POINT`.

| `N` | selected `eta` | selected objective | archived objective | result |
|---:|---:|---:|---:|:---|
| 5 | 1.5274351309 | 0.6139076864 | 0.614 | PASS |
| 10 | 1.3709257755 | 0.3454645531 | 0.345 | PASS |
| 30 | 1.2496030738 | 0.1297734097 | 0.130 | PASS |

The detailed curves are `validation_avg_eta_curve_N{5,10,30}.csv`; aggregate
metadata are in `validation_avg_summary.csv` and `AltGDA_avg_5_30.jld`.

## Last-iterate pilot

For `N` in `{5,10,15}`, each 25-point global curve had objective range below
`1.5e-6`, so all three were classified as flat under the predeclared `1e-3`
threshold. The required archived ergodic-optimal stepsize was then evaluated
and selected, giving objectives within `1.4e-6` of 2. All 78 solves had the
strict status triple above. This is a GO decision for the requested
`N = 5:30` sweep, not a rate claim.

The detailed curves are `pilot_lst_eta_curve_N{5,10,15}.csv`; aggregate
metadata are in `pilot_lst_summary.csv` and `AltGDA_lst_5_15.jld`. The fitted
runtime plan is in `pilot_lst_shard_plan.csv`. Its `0.27`-hour prediction is
based on median solver times and the prescribed twofold safety factor.

## Last-iterate sweep: COMPLETE

S02 ran the authoritative last-iterate study at every integer horizon
`N = 5:30`; no `N = 31:50` sweep was run or planned. MOSEK used
`MSK_DPAR_INTPNT_CO_TOL_PFEAS = 1e-4` and
`MSK_DPAR_INTPNT_CO_TOL_DFEAS = 1e-4` throughout. All 676 retained stepsize
points had status `OPTIMAL / FEASIBLE_POINT / FEASIBLE_POINT`, all 26 horizons
had exactly one selected point, and all were classified as flat under the
predeclared threshold. The aggregate decision is `COMPLETE`.

The sweep artifacts are:

- `sweep_lst_eta_curve_N5.csv` through `sweep_lst_eta_curve_N30.csv`, one full
  retained curve per horizon;
- `sweep_lst_summary.csv`, the 26-row status, classification, selection, and
  runtime summary; and
- `AltGDA_lst_5_30.jld`, the JLD2 aggregate containing all curve rows,
  summaries, and selected-result payloads.

S02 reused the semantically validated S01 pilot checkpoints at
`N in {5,10,15}`, so their 78 points were not solved again. These lightweight
checkpoints preserve objectives, statuses, tolerances, runtimes, and selected
points, but not selected Gram matrices or `nu`. The final aggregation also
loaded completed S02 checkpoints for `N in {6,7}`. Selected-result fields
`G_xv`, `G_uy`, and `nu` for `N in {5,6,7,10,15}` in
`AltGDA_lst_5_30.jld` are therefore `nothing`;
their scalar/status/tolerance/runtime/selection rows remain complete. The
`N=8` search resumed 13 cached points but completed its selected solve live,
so its selected Gram data are retained. Selected Gram matrices and `nu` are
also present for the other 20 horizons.

`COMPLETE` means that the exact `N = 5:30` artifact and strict solver-status
gates passed, including semantic CSV/JLD2 reload. At the formulation level,
the SDP optimum equals the finite-horizon worst case over the modeled class;
the saved floating-point values remain subject to the recorded tolerances and
do not establish an asymptotic rate.

## S04 export, fit, and figure data: COMPLETE

`../export_lastiterate_figures.jl` reloads and validates all 26 summaries,
all 26 curve files (676 rows), and `AltGDA_lst_5_30.jld` before it writes any
derived data. It uses the bundled, three-decimal averaged-gap comparison in
`pep_optimized_stepsizes_altgda.csv`, restricted to the common horizons
`T=5:30` as fixed by roadmap decision D1.

The generated files are:

- `pep_lastiterate_optimized_stepsizes_altgda.csv`, with the exact required
  schema `T,optimized_eta,optimized_duality_gap` and 26 rows;
- `pep_ergodic_lastiterate_gap_figure_data.csv`, the Fig. L1 values and
  precomputed guide lines;
- `pep_ergodic_lastiterate_eta_figure_data.csv`, the Fig. L2 selected
  stepsizes and their differences from the rounded archive;
- `pep_ergodic_lastiterate_loglog_fit_summary.csv`, four natural-log OLS
  fits; and
- `pep_ergodic_lastiterate_loglog_fit_points.csv`, the 84 underlying
  full-window/tail-window fit points.

The fixed inclusive fit windows are `T=5:30` (26 points) and `T=15:30`
(16 points). The archived averaged-gap slopes are `-0.8820329597` and
`-0.9112375275`; the selected last-iterate slopes are
`-7.5134e-9` and `1.1540e-8`. Last-iterate objectives vary only at solver
scale around 2, so those slopes are interpreted as numerically flat. They do
not establish a zero asymptotic exponent, a nonconvergence result, or a lower
bound for the original algorithm.

The predeclared interpretation gate is
`abs(tail_slope + 1) <= 0.25` on the `T=15:30` last-iterate fit. If it fires,
the exporter retains the diagnostics but requires a user decision before
manuscript work. It did not fire for the current `1.1540e-8` tail slope.

For Fig. L1, the `T^-1` guide is anchored to the archived averaged-gap value
at `T=5`, while the `T^-1/2` guide is anchored to the selected last-iterate
value at `T=5`. The guides are visual aids, not fitted models or bounds.

The last-iterate filename retains the historical `optimized_*` schema for
compatibility. Since all 26 objective curves were classified flat, the
search rule deliberately selected the archived averaged-gap canonical
stepsize. These values are therefore canonical selections, not uniquely
identified last-iterate optima.

Files with the `.jld` suffix use JLD2, not the legacy JLD package.
