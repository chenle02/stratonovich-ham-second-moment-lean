# Slurm lower-tier receipt (wave L10, Easley stage 2, second run)

The second stage-2 run approved by the author on 2026-11-12 (the first was
the wave-L9 pilot, `verification/slurm-receipt-pilot-wave-l9/`): the
lower-tier receipt produced by `lean-pkg receipt slurm` on Easley, compared
with the local systemd receipt at the same commit. It is evidence of
reproducibility, not the gate receipt; the gate receipts are in
`.lean-receipts/b2bf7a921fb8-*` (local systemd and comparator).

- Commit: `b2bf7a9` (wave L10 merged into main). Job 5696226, COMPLETED 0:0,
  1:16:40 elapsed, TotalCPU 1:32:18, MaxRSS 7,084,464 KB, 4 CPUs / 12G, lab
  container (`<container>.sif`, SIF sha256 `0639ce71…`, the same image as in
  the pilot).
- `verify.sbatch`: the pilot's file with two changes, the job name
  (`stratham-l10-receipt`) and the wave named in its header comment. The
  short trial job of the pilot was not repeated: the wrapper is otherwise
  byte-identical and `--check` passed on the real job's files.
- `check-5696226.txt`: `lean-pkg receipt slurm --check` output (ok on every
  item, sacct from a saved `sacct -n -P` copy).
- `b2bf7a921fb8-slurm-5696226.json` and the redacted verify log: the receipt.
- `compare-local-vs-slurm.txt`: field-by-field comparison with the local
  receipt (`compare.py` of the pilot, unchanged). Same commit, toolchain,
  Mathlib, manifest, build line (9158 jobs), 2988 axiom lines, sorry count 0,
  2757 claims with identical per-claim axiom sets and identical hyp-probe
  output; only the checker name, the shadow-check line, job metadata and
  timing differ.

With the wave-L9 pilot, this is the second clean stage-2 run.
