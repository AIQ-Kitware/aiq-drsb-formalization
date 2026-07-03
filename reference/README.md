# `reference/` — old attempts, **reference-only (treat with caution)**

These files are **earlier, un-audited attempts** at DRSB-related results. They are
kept for reference — parts of them (definitions, proof tactics, and especially the
*proved* Donsker–Varadhan / Hoeffding lemmas in `WellKnown.lean`) will likely be
useful — **but they are not canon and contain subtle traps.**

> ⚠️ Do **not** copy a theorem *statement* from here into the new libraries without
> checking it against the transcribed paper in [`../prose/`](../prose/). Several
> statements here are "close to, but slightly different from" the published results
> (missing hypotheses, a flipped inequality direction, an estimator that does not
> match the theorem, etc.). The whole point of the new scaffold is to re-derive the
> statements *from the papers*, not from these files.

They are **not** part of the Lake build (not listed as `lean_lib`s in
`lakefile.toml`), so `lake build` ignores them.

| File | What it attempted |
|---|---|
| `V1.lean` | TwoPager Theorem 4 (PAC-Bayes for the clipped terminal-cost net `g`), Eqs. (116)–(126). |
| `V4.lean` | Full DRSB scaffold: SB/SOC value function, WDRO/SDRO ambiguity sets + duals, Gibbs worst-case, `M_logPartition`, the empirical dual, and the TwoPager BCE→Hoeffding→DV→PAC-Bayes chain. |
| `WellKnown.lean` | The genuinely-proved building blocks: Hoeffding MGF bound, and the **Donsker–Varadhan** inequality / variational (Gibbs) form (`integral_le_klDiv_add_log_integral_exp`, `isGreatest_donskerVaradhan`, `log_integral_exp_eq_sSup`). These are the best salvage candidates for `ForMathlib`. |
| `old-attempt/drsb-v2.lean`, `drsb-v3.lean`, `drsb-v3.1.lean` | Progressively-revised TwoPager Theorem-4 skeletons. |

When a result here is validated against the prose and promoted into a new library,
delete it from this note (or mark it "promoted → `<Lib>/<file>`").
