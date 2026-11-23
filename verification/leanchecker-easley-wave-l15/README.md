# External kernel replay on Easley, wave L15 (`leanchecker --fresh`, array gate, 2026-11-20)

Verification evidence at 315a3327dfc8: Easley leanchecker replay of wave L15 (4/4).

This is an independent replay of commit `315a332` on Auburn's Easley cluster
(Slurm). `315a332` is the head of the wave-L15 integration branch
(`wave-l15/int`). It is the seventh **array** gate, with the harness of the
wave-L9 to wave-L14 gates: every harness script (`stage-login.sh`,
`preflight-login.sh`, `build.sbatch`, `task.sbatch`, `submit.sh`,
`collect.py`, `replay.py`) is byte-identical to the wave-L13/L14 folder's,
as are `make-inputs.sh` (after redaction) and `closure-check.py`. `pins.env`,
`modules-all.txt`, `targets-fresh.txt` and `INPUT-SHA256SUMS` name this
commit.

Unlike the wave-L9 to wave-L14 gates, only the **four new library modules**
of wave L15 are replayed `--fresh` (the scope asked for this gate):

```
StratonovichHAMSecondMoment.PositiveRawMean
StratonovichHAMSecondMoment.UniformELift
StratonovichHAMSecondMoment.UniformMeanFoundation
StratonovichHAMSecondMoment.UniformMeanInterface
```

`targets-fresh.txt` is this list (made by `make-inputs.sh ... all` and then
replaced by these four lines, with `INPUT-SHA256SUMS` recomputed). Array task
`i` (1 to 4) replays its line `i` with `lake env leanchecker --fresh`, which
also re-checks every transitive import (Lean core, Batteries, the imported
Mathlib slice and the project modules the target imports). Array task 0
replays all 146 manifest targets (`modules-all.txt`: 145 library modules and
the umbrella) in default mode, as at every array gate.

**Result.** All 4 `--fresh` targets exit 0 with empty output, which is the
pass signature. All 146 targets pass default-mode replay
(`default/summary-5731618.tsv`). The build job and all 5 array tasks ended
`COMPLETED 0:0`, each with one attempt; no task was resubmitted.
`collect.py` exited 0 with verdict `COMPLETE` (`COLLECT.txt`).

| Module | `--fresh` | wall | peak RSS (KiB) | default-mode wall |
|---|---|---|---|---|
| `PositiveRawMean` | pass | 0:43:09.98 | 7,616,068 | 0:00:09.78 |
| `UniformELift` | pass | 0:43:48.89 | 7,614,364 | 0:00:09.17 |
| `UniformMeanFoundation` | pass | 0:43:39.29 | 7,613,704 | 0:00:11.13 |
| `UniformMeanInterface` | pass | 0:43:48.21 | 7,611,864 | 0:00:16.17 |

## Coverage

`harness/closure-check.py` (unchanged since wave L5), run locally on
`8f51004` (the wave-L13/L14 replay commit, all 142 targets `--fresh`) against
`315a332`, gives (`harness/closure-check.txt`): 4 new modules (the four
above), 1 changed in content (the umbrella, which imports them), 111 changed
only in comments, all with unchanged line counts (manuscript line references
in module docstrings), 30 byte-identical, none removed, and one
import-closure gap, `Axioms`, which imports the umbrella.

So at `315a332` the four new modules are replayed `--fresh`; the umbrella and
`Axioms` are replayed in default mode only (task 0), and the other 140
modules are covered `--fresh` by the wave-L13/L14 replay at `8f51004` up to
comment-only changes, plus default mode here. This folder does **not** claim
that every library module has passed a `--fresh` replay at `315a332`.

**Not covered.** The comparator-tier Lake libraries `ChallengeDefs`,
`Challenge` and `Solution` are not imported by the umbrella and are not
built by `lake build StratonovichHAMSecondMoment`. This replay does not
check them.

## What was checked

| Item | Value |
|---|---|
| Commit | `315a3327dfc8acc964a874962756fbcc28ff1687` |
| Tree | `5abf7fdde0d2f2940d50d340ae0f095c9bbd150e` (checked by the build job before and after the build, and by every task before and after its replay) |
| Toolchain | `leanprover/lean4:v4.35.0`; Lean 4.35.0 (commit `eb6cafb7290e`), Lake 5.0.0 |
| Mathlib | `56a005855ea17e0b0958f73ec801ae140b0a1679`, checked by the build job and again by every task |
| `leanchecker` binary | sha256 `12c38901cdbfab178f1bf6145dd30012e9a3b2c11ca695292a5884fa3cbaddb6` (`lean` `bf8d54e4…`, `lake` `8ba83c98…`), the same binaries as in the wave-L5 to wave-L14 replays |
| Runtime | Lean 4.35.0 runtime tarball (sha256 `9bca7d29…`), extracted on the compute node, run inside the lab Apptainer image (Ubuntu 22.04) with `--cleanenv` |
| Workspace | the build job's sealed tarball `ws.tar.gz`, 2,578,298,199 bytes, sha256 `c245e2e7…c1bea`; every counted task checked this hash before unpacking |
| Host | Easley, partition `nova_20`, QOS `resourcecap_plus`. Build and pilot on node835; tasks 0, 2, 3, 4 on node836 to node839, one per node |
| Build | `lake build StratonovichHAMSecondMoment StratonovichHAMSecondMoment.Axioms`: "Build completed successfully (9193 jobs)."; all 146 `.olean` files present |

`collect.py` binds every counted task to the build (commit, tree, inputs
hash, workspace tarball hash, `leanchecker` hash), checks that its target is
its manifest line and that its summary lists exactly that target with exit 0
and 0 output bytes (task 0: exactly the 146 manifest targets), and that
sacct shows the task `COMPLETED 0:0`.

## Commands

The private development repository was cloned on the login node over GitHub
ssh and `315a332…` was checked out detached (`harness/stage-login.sh`). The
login node was reached through the <MACHINE> machine's connection (from the
laptop, `ssh <MACHINE> "ssh Easley bash -s"`); the frozen inputs were sent and
the evidence fetched the same way. `harness/preflight-login.sh` (with 2 CPUs
per task) passed before any submission (`MANIFEST_OK modules=146
fresh_targets=4`; the container has git, lake, lean, leanchecker, python3,
timeout, curl, tar, gzip and sha256sum on the job's PATH; output in
`harness/preflight/`).

Submission (`harness/submit.sh` with `CPUS=2 MEM=48G`, record in
`jobs.txt`):

```
sbatch build.sbatch                                                          # 5731611, --cpus-per-task=4 --mem=24G
sbatch --dependency=afterok:5731611 --array=1 --cpus-per-task=2 --mem=48G task.sbatch    # pilot 5731612
sbatch --array=0,2-4%100 --cpus-per-task=2 --mem=48G task.sbatch                         # rest 5731617
```

The rest was submitted once the pilot printed `REPLAY_STARTED`. Inside the
container (`PATH=<runtime>/bin:/usr/bin:/bin`, `LEAN_NUM_THREADS=3`,
`LAKE_ARTIFACT_CACHE=false`) each task ran

```
timeout -k 30s 3600s  lake env leanchecker <Module>           # task 0: default mode, all 146 targets, serial
timeout -k 30s 14400s lake env leanchecker --fresh <Module>   # task i >= 1: line i of targets-fresh.txt
```

**Open files.** No task waited for the `file-nr` guard (all `waited_s=0`,
`PRE_REPLAY file-nr` 1,280 to 1,440); the largest `file-nr` sample in the
monitors was 62,520.

## Accounting (sacct)

| Job | Role | Elapsed | TotalCPU | Alloc | MaxRSS (batch) |
|---|---|---|---|---|---|
| 5731611 | build | 0:22:37 | 0:51:49 | 4 CPU / 24G | 7,102,260 KB |
| 5731612 (`5731612_1`) | `--fresh` `PositiveRawMean` | 0:45:21 | 0:45:02 | 2 CPU / 48G | 7,819,080 KB |
| 5731619 (`5731617_2`) | `--fresh` `UniformELift` | 0:45:58 | 0:45:47 | 2 CPU / 48G | 7,830,540 KB |
| 5731620 (`5731617_3`) | `--fresh` `UniformMeanFoundation` | 0:45:58 | 0:45:35 | 2 CPU / 48G | 8,058,044 KB |
| 5731617 (`5731617_4`) | `--fresh` `UniformMeanInterface` | 0:46:54 | 0:45:45 | 2 CPU / 48G | 7,254,100 KB |
| 5731618 (`5731617_0`) | default mode, 146 targets | 0:38:46 | 0:45:01 | 2 CPU / 48G | 24,324,468 KB |

Build phases: `lake exe cache get` 70 s (first attempt), build 850 s,
tarball 211 s. Task 0 replay phase 2,218 s for 146 targets (the umbrella
alone 0:11:48, peak RSS 25,076,712 KiB). Totals: 4:05:34 elapsed over the
six jobs, TotalCPU 4:38:59.

**Wall time.** Build and pilot submitted 2026-11-20 01:03:05 CST; the rest
at 01:29:13; the last task ended at 02:16:08. From first submission to the
last task: **1:13:03**.

## Files

As in the wave-L13/L14 folder: `summary.tsv` (one row per `--fresh` target:
module, exit, wall, peak RSS KiB, output bytes, job id), `fresh-time/`,
`default/summary-5731618.tsv`, `jobs/<job>/` (build logs and `BUILD_OK`;
per task `task.log`, `monitor.log`, `task.result`), `COLLECT.txt`,
`sacct.tsv`, `sacct-submit.tsv`, `jobs.txt`, and `harness/` (frozen inputs,
`make-inputs.sh`, `preflight/`, `closure-check.py` and
`closure-check.txt`).

The HPC username is redacted to `<user>`, the container image path to
`<container>.sif` and the runtime directory name to `<runtime-dir>` in every
file of this folder. Of the hashed inputs only `pins.env` contained them, so
its hash now differs from the one in `harness/INPUT-SHA256SUMS`;
`sha256sum -c` reports OK for the other nine files. The job names
(`stratham-l11-build`, `stratham-l11-lchk`) come from the harness, which was
prepared for wave L11. No cluster lower-tier receipt was made at this commit.

For the public release, the name of a local workstation was further replaced by `<MACHINE>` in this README (the connection path to the login node) and in `make-inputs.sh` (comments only).
