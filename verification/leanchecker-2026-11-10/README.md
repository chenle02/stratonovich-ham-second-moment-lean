# External kernel replay with leanchecker (2026-11-10)

`lake env leanchecker <Module>` replays the stored declarations of each
compiled module through the Lean kernel, a layer beyond `lake build` and
`#print axioms` (see the Lean reference, "Validating a Lean Proof").

- Tree: commit `8b77aba`, a docs-only descendant of the lean-pkg receipt
  commit `b876362` (identical build inputs, so the replayed `.olean` files are
  the receipted ones). Lean 4.35.0, Mathlib `56a0058`.
- Mode: default (the named package modules are re-checked; imported Mathlib
  `.olean` files are trusted). A `--fresh` replay of the transitive imports is
  heavier and is planned as a cluster job.
- Result: all 31 modules (23 `StratonovichHAMAudit`, 7 `StratonovichHAMSecondMoment`,
  and the axiom report) and the umbrella import exit 0 with empty output, the
  pass signature. `summary.tsv` columns: module, exit code, wall time, peak RSS
  (KiB), output bytes. The `.time` files are the `/usr/bin/time -v` records.
- Note: one invocation naming all 31 modules at once did not finish within
  30 minutes; per-module invocations take 3–5 s each (peak 6.4 GiB).
