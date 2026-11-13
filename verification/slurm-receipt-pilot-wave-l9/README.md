# Slurm lower-tier receipt pilot (wave L9, Easley stage 2)

Pilot approved by the author on 2026-11-12: the lower-tier receipt produced by
`lean-pkg receipt slurm` on Easley, compared with the local systemd receipt at the
same commit. It is evidence of reproducibility, not the gate receipt; the gate
receipts are in `.lean-receipts/6eb79c7b2ec4-*` (local systemd and comparator).

- Commit: `6eb79c7` (wave L9 merged into main). Job 5695604, COMPLETED 0:0, 1:08:49
  elapsed, 4 CPUs / 12G, lab container (`<container>.sif`).
- `verify.sbatch`: the `lean-pkg receipt slurm --template` wrapper adapted to this
  package (build of the umbrella and the Axioms module; axioms from the Axioms module).
- `check-5695604.txt`: `lean-pkg receipt slurm --check` output (ok on every item).
- `6eb79c7b2ec4-slurm-5695604.json` and the redacted verify log: the receipt.
- `compare-local-vs-slurm.txt`: field-by-field comparison with the local receipt.
  Same commit, toolchain, Mathlib, manifest, build line (9150 jobs), 2688 axiom
  lines, sorry count 0, 2468 claims with identical per-claim axiom sets and
  identical hyp-probe output; only job metadata and timing differ.
