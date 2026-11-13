# External kernel replay on Easley, wave L8 (`leanchecker --fresh`, array gate, 2026-11-12)

This is an independent replay of commit `aff7409` on Auburn's Easley cluster
(Slurm). `aff7409` is the commit at which the wave-L8 correspondence gate
closed (see the README on main). It is the seventh Easley gate and the first
**array** gate: one build job builds the library once from a fresh clone and
seals the workspace, and a Slurm job array then replays one target per
task, each task at 2 CPUs and 36G. Every one of the 92 targets (91 library
modules plus the umbrella) is replayed by its own
`lake env leanchecker --fresh <Module>` run, which also re-checks every
transitive import (Lean core, Batteries and the imported Mathlib slice).
Array task 0 replays all 92 targets in default mode.

**Result.** All 92 `--fresh` targets exit 0 with empty output, which is the
pass signature. All 92 targets also pass default-mode replay
(`default/summary-5692934.tsv`). The build job and all 93 array tasks ended
`COMPLETED 0:0`, each with one attempt; no task was resubmitted.

Because every target was replayed `--fresh` at `aff7409`, this folder needs
no replay-coverage argument (unlike the wave-L5 to wave-L7 folders, which
covered unchanged modules through earlier replays). Every library module
through wave L8 has passed a `--fresh` replay, here at a single commit.

## Covered modules

All 92 lines of `harness/modules-all.txt`: the 24 `StratonovichHAMAudit`
modules, the 67 `StratonovichHAMSecondMoment` modules (including `Axioms`)
and the umbrella `StratonovichHAMSecondMoment`. `harness/targets-fresh.txt`
is the same list (same sha256), and array task `i` (1 to 92) replays its
line `i`. `modules-all.txt` equals the `StratonovichHAMAudit` and
`StratonovichHAMSecondMoment` source files at `aff7409`, sorted, plus the
umbrella (checked again with `git ls-tree` when this folder was written; the
build job also checked it, `MANIFEST_OK modules=92`).

### Import-closure check

The L11 array harness has no closure-check step: with every target replayed
`--fresh`, it is not needed for coverage. For the record,
`harness/closure-check.py` (the wave-L5 script, same sha256 as in the
wave-L5 to wave-L7 folders) was run on a local checkout. Its output is in
`harness/closure-check.txt`:

- relative to the wave-L7 replay commit `f3be834`: 11 new modules (the
  wave-L8 modules `DampedMultiplier`, `FiniteWick`, `L8Completed`,
  `OccupationCeilingFinite`, `RemoveMask`, `SpaceTimePositivity`,
  `SpatialBracket`, `SpectralMassIdentity`, `StaticPhaseCauchy`,
  `SymplecticFree`, `TerminalWick`), 2 changed in content (the umbrella and
  `Axioms`), 0 changed only in comments, 79 byte-identical, none removed,
  0 import-closure gaps;
- relative to `ff40157` (origin/main when this folder was written): all 92
  modules byte-identical, none new or removed.

**Not covered.** The three comparator-tier Lake libraries `ChallengeDefs`,
`Challenge` and `Solution` are not imported by the umbrella and are not built
by `lake build StratonovichHAMSecondMoment`. This replay does not check them.

## What was checked

| Item | Value |
|---|---|
| Commit | `aff740933af2ffa57d33bb8294dd0b6fa5680105` |
| Tree | `488dea9b68d368b60b7c07c35a4208354e470e55` (checked by the build job before the build and after it, and by every task before and after its replay) |
| Library sources vs later main | **identical**: `git diff --stat aff7409 ff40157 -- 'StratonovichHAM*' lakefile.toml lake-manifest.json lean-toolchain` is empty (`ff40157` was origin/main when this folder was written) |
| Toolchain | `leanprover/lean4:v4.35.0`; Lean 4.35.0 (commit `eb6cafb7290e`), Lake 5.0.0 |
| Mathlib | `56a005855ea17e0b0958f73ec801ae140b0a1679`; the build job checked this pin after `lake exe cache get`, and every task checked it again in its unpacked workspace |
| `leanchecker` binary | sha256 `12c38901cdbfab178f1bf6145dd30012e9a3b2c11ca695292a5884fa3cbaddb6` (`lean` `bf8d54e4…`, `lake` `8ba83c98…`), the same binaries as in the wave-L5 to wave-L7 replays; every task checked its unpacked `leanchecker` and `lean` against the build job's hashes |
| Runtime | Lean 4.35.0 runtime tarball (sha256 `9bca7d29…`, checked by every job), extracted on the compute node, run inside the lab Apptainer image (Ubuntu 22.04, glibc 2.35) with `--cleanenv` |
| Workspace | the build job's sealed tarball `ws.tar.gz`, 2,515,813,077 bytes, sha256 `55627a64…c14215`; every counted task checked this hash before unpacking |
| Host | Easley, partition `nova_20`, QOS `resourcecap_plus`. Build job on node832; pilot (task 1) and task 0 also on node832, one after the other; every other task alone on its own node (91 nodes) |
| Build | `lake build StratonovichHAMSecondMoment StratonovichHAMSecondMoment.Axioms`: "Build completed successfully (9139 jobs)."; `ALL_OLEANS_PRESENT=92` |

The full build log has 2309 `#print axioms` messages and no Lean warnings.
2287 declarations depend on `[propext, Classical.choice, Quot.sound]`, two on
`[propext, Quot.sound]`, nine on `[propext]` and eleven on no axioms. No
declaration depends on `sorryAx`. Only the tail is kept here
(`jobs/5692847/build.tail.log`).

`collect.py` binds every counted task to the build: the task's commit, tree,
inputs hash, workspace tarball hash and `leanchecker` hash must equal those
in `BUILD_OK`, its target must equal its manifest line, its summary must list
exactly that target with exit 0 and 0 output bytes (task 0: exactly the 92
manifest targets), and sacct must show the task `COMPLETED 0:0`. Its verdict
(`COLLECT.txt`) is `COMPLETE`: 92 of 92 `--fresh` targets counted, default
mode passed, nothing to resubmit, no problems, no failure signatures.

## Commands

The private repository was cloned on the login node over GitHub ssh, and
`aff740933af2…` was checked out detached. The build job copied that clone,
without `.lake`, to node-local `/tmp`. Inside the container, with
`PATH=<runtime>/bin:/usr/bin:/bin`, `LEAN_NUM_THREADS=3` and
`LAKE_ARTIFACT_CACHE=false`, it ran:

```
lake exe cache get
lake build StratonovichHAMSecondMoment StratonovichHAMSecondMoment.Axioms
```

checked that all 92 `.olean` files exist and that the source was unchanged,
and packed the workspace (sources, `.lake` with Mathlib and the project
`.olean` files) into `ws.tar.gz`, recording its hash in `BUILD_OK`.

Each array task copied the image and the runtime to node-local `/tmp`,
unpacked the sealed workspace, checked commit, tree, clean status, Mathlib
pin and the presence of its target's `.olean`, and ran, in the same container
setting:

```
timeout -k 30s 3600s  lake env leanchecker <Module>           # task 0: default mode, all 92 targets, serial
timeout -k 30s 14400s lake env leanchecker --fresh <Module>   # task i >= 1: line i of targets-fresh.txt
```

It then checked again that the tree was unchanged and clean.

Submission (`harness/submit.sh`, record in `jobs.txt`):

```
sbatch build.sbatch                                   # --cpus-per-task=4 --mem=24G
sbatch --dependency=afterok:<build> --array=1 --cpus-per-task=2 --mem=36G task.sbatch       # pilot
sbatch --array=0,2-92%100 --cpus-per-task=2 --mem=36G task.sbatch                            # rest
```

All three with `--time=1-00:00:00 --no-requeue`. The rest was submitted
after the pilot task had passed. `--mem=36G` caps the packing at three tasks
per 128 GB node, which keeps the node-wide open-file limit (262,144) safe
(one `--fresh` run holds about 62k open files). As scheduled, every task had
its node to itself. Each task also waited before its replay while the node's
`/proc/sys/fs/file-nr` exceeded 190,000; no task had to wait (all
`waited_s=0`, `PRE_REPLAY file-nr` between 1,240 and 1,640).

Before any submission, `harness/preflight-login.sh` checked the inputs, the
container and the runtime on the login node (`harness/preflight/`;
`PREFLIGHT_OK` holds the sha256 of `INPUT-SHA256SUMS`). Its sandbox probe
(`preflight-sandbox.log`) records that unprivileged user namespaces are not
available on the login node; the jobs use the Apptainer image, not a sandbox.

The harness is the L11 array harness, new in this gate. `replay.py` is the
script of the wave-L5 to wave-L7 replays, unchanged (sha256 `10e90176…`). The
image has no `/usr/bin/time`, so `replay.py` takes each run's peak RSS and
CPU time from `os.wait4` on that run's process. The `.time` files show
`Job: NA` because `--cleanenv` hides `SLURM_JOB_ID`; the job id is the last
column of `summary.tsv`.

The Singularity `HOME` notice of the wave-L5 to wave-L7 logs does not occur:
this harness does not pass `HOME` in the `--env` list.

## Accounting (sacct)

Per array task (93 tasks, each 2 CPUs / 36G; `sacct.tsv`):

| Tasks | Elapsed min / median / max | TotalCPU min / median / max | MaxRSS (batch) min / median / max |
|---|---|---|---|
| 92 `--fresh` (tasks 1–92) | 0:09:12 / 0:47:51 / 0:52:42 | 0:03:59 / 0:43:47 / 0:45:37 | 1,049,508 / 7,055,858 / 8,068,492 KB |
| all 93 (with task 0) | 0:09:12 / 0:47:42 / 0:52:42 | 0:03:59 / 0:43:47 / 0:45:37 | 1,049,508 / 7,058,848 / 16,545,800 KB |

Task 0 (default mode, `5692933_0` = job 5692934): elapsed 0:20:25,
TotalCPU 0:25:14, MaxRSS 16,545,800 KB; replay phase 1,128 s for 92 targets.
Build job 5692847: elapsed 0:12:36, TotalCPU 0:27:17 on 4 CPUs / 24G,
MaxRSS 6,984,272 KB; phases `cache get` 74 s, build 380 s, tarball 204 s.

The `--fresh` replays themselves (`summary.tsv`, from `os.wait4`): wall
0:02:08.69 (`StratonovichHAMAudit.HermiteWordConsumer`) / median 0:41:55.68 /
0:43:44.08 (`StratonovichHAMSecondMoment.Axioms`); peak RSS 692,384 /
median 7,572,266 / 7,750,824 KiB (umbrella). The total `--fresh` wall time
over the 92 runs is 179,896 s (about 50.0 h). The rest of each task's elapsed
time is the start stagger (`sleep` of `(11 i) mod 301` s), the copy and
unpacking of image, runtime and workspace, and the checks.

Totals over the 93 tasks: elapsed 61:35:25 (123:10:50 allocated core-hours at
2 CPUs), TotalCPU 53:13:46. One `--fresh` run uses about one core, so a task
uses about 43% of its two CPUs (median TotalCPU / (2 × Elapsed) 0.433).

The cgroup memory peak (page cache included, `monitor.log`) was 22.5 GB for
the `--fresh` tasks and 29.5 GB for task 0, out of the 36G request. The
largest `file-nr` sample was 62,880.

**Wall time.** Build and pilot were submitted at 2026-11-12 08:59:10 CST. The
build ran 08:59:11–09:11:47 and the pilot 09:11:48–09:23:49. The rest
(`0,2-92`) was submitted at 09:37:40; all 92 of its tasks started between
09:37:41 and 09:38:09, with no queue wait. The last task ended at 10:30:23.
From first submission to the last task: **1:31:13**; from the submission of
the rest: 0:52:43 (`sacct-submit.tsv`). For comparison, the wave-L7 gate
replayed 10 targets `--fresh` in one 4-CPU job of 4:00:39.

## Files

- `summary.tsv`: one row per `--fresh` target, in manifest order. Columns:
  module, exit code, wall time (h:mm:ss), peak RSS (KiB), output bytes, job
  id (the task's own Slurm job id).
- `fresh-time/<Module>.time`: the record of each `--fresh` run.
- `default/summary-5692934.tsv`: the default-mode replay of all 92 targets
  (task 0).
- `jobs/5692847/` (build job): `build-job.log`, `build-monitor.log`,
  `runtime-preflight.log`, `runtime-binaries.sha256`, `cache-get-1.log`,
  `BUILD_OK`, and `build.tail.log` (the last 13 lines of the build log: the
  last four `#print axioms` messages and the completion line). In
  `build-job.log` and `cache-get-1.log` the carriage returns of the
  cache-download progress line are replaced by newlines, as in the earlier
  folders.
- `jobs/<job>/` for each of the 93 counted tasks: `task.log`, `monitor.log`
  (`file-nr` and cgroup memory every 30 s) and `task.result` (bindings,
  node, start and end).
- `COLLECT.txt`: the verdict of `harness/collect.py`, run on the login node
  as `python3 -I collect.py RUN_DIR OUT_DIR`; it exited 0.
- `sacct.tsv`: the sacct query `collect.py` made (jobs and steps, with
  Elapsed, TotalCPU, ReqMem, MaxRSS, NodeList). `sacct-submit.tsv`: a second
  query, `sacct -P -X -j 5692847,5692848,5692933` with Submit, Eligible,
  Start, End, State, ExitCode, Partition, QOS and NodeList, for the wall
  time.
- `jobs.txt`: the submission record written by `submit.sh`.
- `harness/`: the inputs of the campaign, `build.sbatch`, `task.sbatch`,
  `submit.sh`, `stage-login.sh`, `preflight-login.sh`, `collect.py`,
  `replay.py`, `pins.env`, `modules-all.txt`, `targets-fresh.txt` and
  `INPUT-SHA256SUMS`, which every job checked; `make-inputs.sh`, which froze
  them on a local checkout; `preflight/`, the login-node preflight output;
  `closure-check.py` with its output `closure-check.txt` (run locally, not
  part of the campaign).

The HPC username is redacted to `<user>`, the container image path to
`<container>.sif` and the runtime directory name to `<runtime-dir>` in every
file of this folder. Of the hashed inputs only `pins.env` contained them, so
its hash now differs from the one in `harness/INPUT-SHA256SUMS`;
`sha256sum -c` reports OK for the other nine files. `make-inputs.sh` is
redacted the same way and is not in `INPUT-SHA256SUMS`.
For the public release, the name of a local workstation was further replaced by `<MACHINE>` in `make-inputs.sh` (comments only).
