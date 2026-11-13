# External kernel replay on Easley, wave L9 (`leanchecker --fresh`, array gate, 2026-11-12)

This is an independent replay of commit `6eb79c7` on Auburn's Easley cluster
(Slurm). `6eb79c7` is the merge of wave L9 into main. It is the second
**array** gate, with the harness of the wave-L8 gate unchanged except for one
line of `submit.sh` (see Commands). One build job builds the library once from
a fresh clone and seals the workspace, and a Slurm job array then replays one
target per task, each task at 2 CPUs and 36G. Every one of the 103 targets
(102 library modules plus the umbrella) is replayed by its own
`lake env leanchecker --fresh <Module>` run, which also re-checks every
transitive import (Lean core, Batteries and the imported Mathlib slice).
Array task 0 replays all 103 targets in default mode.

**Result.** All 103 `--fresh` targets exit 0 with empty output, which is the
pass signature. All 103 targets also pass default-mode replay
(`default/summary-5695615.tsv`). The build job and all 104 array tasks ended
`COMPLETED 0:0`, each with one attempt; no task was resubmitted.

Every target was replayed `--fresh` at `6eb79c7`, so this folder needs no
replay-coverage argument. Every library module through wave L9 has passed a
`--fresh` replay, here at a single commit.

## Covered modules

All 103 lines of `harness/modules-all.txt`: the 25 `StratonovichHAMAudit`
modules, the 77 `StratonovichHAMSecondMoment` modules (including `Axioms`)
and the umbrella `StratonovichHAMSecondMoment`. `harness/targets-fresh.txt`
is the same list (same sha256), and array task `i` (1 to 103) replays its
line `i`. `modules-all.txt` equals the `StratonovichHAMAudit` and
`StratonovichHAMSecondMoment` source files at `6eb79c7`, sorted, plus the
umbrella (checked by `harness/preflight-login.sh` on the staged clone and by
the build job, `MANIFEST_OK modules=103`).

### Import-closure check

As in wave L8, the array harness has no closure-check step: with every target
replayed `--fresh`, it is not needed for coverage. For the record,
`harness/closure-check.py` (the wave-L5 script, same sha256 as in the
wave-L5 to wave-L8 folders) was run on a local checkout. Its output is in
`harness/closure-check.txt`:

- relative to the wave-L8 replay commit `aff7409`: 11 new modules
  (`StratonovichHAMAudit.HermiteWordFock` and the wave-L9 modules
  `ComplexPhaseScalar`, `FockForm`, `GaussianHermite`, `HermiteFock`,
  `L9Completed`, `LowAlphaConvolution`, `OccupationCeilingExact`,
  `PhaseContractions`, `RawOccupationEnergy`, `WaveGreenFourier`), 2 changed
  in content (the umbrella and `Axioms`), 0 changed only in comments,
  90 byte-identical, none removed, 0 import-closure gaps;
- relative to `b18037b` (origin/main when this folder was written): all 103
  modules byte-identical, none new or removed.

**Not covered.** The three comparator-tier Lake libraries `ChallengeDefs`,
`Challenge` and `Solution` are not imported by the umbrella and are not built
by `lake build StratonovichHAMSecondMoment`. This replay does not check them.

## What was checked

| Item | Value |
|---|---|
| Commit | `6eb79c7b2ec4ca52f02121224484aa4865e43ac8` |
| Tree | `de6f79a14664bfad0e9c60dff29dc2f0ed37711e` (checked by the build job before the build and after it, and by every task before and after its replay) |
| Library sources vs later main | **identical**: `git diff --stat 6eb79c7 b18037b -- 'StratonovichHAM*' lakefile.toml lake-manifest.json lean-toolchain` is empty (`b18037b` was origin/main when this folder was written) |
| Toolchain | `leanprover/lean4:v4.35.0`; Lean 4.35.0 (commit `eb6cafb7290e`), Lake 5.0.0 |
| Mathlib | `56a005855ea17e0b0958f73ec801ae140b0a1679`; the build job checked this pin after `lake exe cache get`, and every task checked it again in its unpacked workspace |
| `leanchecker` binary | sha256 `12c38901cdbfab178f1bf6145dd30012e9a3b2c11ca695292a5884fa3cbaddb6` (`lean` `bf8d54e4…`, `lake` `8ba83c98…`), the same binaries as in the wave-L5 to wave-L8 replays; every task checked its unpacked `leanchecker` and `lean` against the build job's hashes |
| Runtime | Lean 4.35.0 runtime tarball (sha256 `9bca7d29…`, checked by every job), extracted on the compute node, run inside the lab Apptainer image (Ubuntu 22.04, glibc 2.35) with `--cleanenv` |
| Workspace | the build job's sealed tarball `ws.tar.gz`, 2,526,942,402 bytes, sha256 `bc9a6334…a4983256`; every counted task checked this hash before unpacking |
| Host | Easley, partition `nova_20`, QOS `resourcecap_plus`. Build job on node855; the pilot (task 1) and tasks 91 and 103 also ran on node855. The 104 tasks ran on 91 distinct nodes, at most three per node |
| Build | `lake build StratonovichHAMSecondMoment StratonovichHAMSecondMoment.Axioms`: "Build completed successfully (9150 jobs)."; `ALL_OLEANS_PRESENT=103` |

The full build log has 2688 `#print axioms` messages and no Lean warnings.
2661 declarations depend on `[propext, Classical.choice, Quot.sound]`, three
on `[propext, Quot.sound]`, 13 on `[propext]` and 11 on no axioms. No
declaration depends on `sorryAx`. Only the tail is kept here
(`jobs/5695590/build.tail.log`, the last 60 lines of the build log).

`collect.py` binds every counted task to the build: the task's commit, tree,
inputs hash, workspace tarball hash and `leanchecker` hash must equal those
in `BUILD_OK`, its target must equal its manifest line, its summary must list
exactly that target with exit 0 and 0 output bytes (task 0: exactly the 103
manifest targets), and sacct must show the task `COMPLETED 0:0`. Its verdict
(`COLLECT.txt`) is `COMPLETE`: 103 of 103 `--fresh` targets counted, default
mode passed, nothing to resubmit, no problems, no failure signatures.

## Commands

The private repository was cloned on the login node over GitHub ssh, and
`6eb79c7b2ec4…` was checked out detached (`harness/stage-login.sh`). The
build job copied that clone, without `.lake`, to node-local `/tmp`. Inside the
container, with `PATH=<runtime>/bin:/usr/bin:/bin`, `LEAN_NUM_THREADS=3` and
`LAKE_ARTIFACT_CACHE=false`, it ran:

```
lake exe cache get
lake build StratonovichHAMSecondMoment StratonovichHAMSecondMoment.Axioms
```

checked that all 103 `.olean` files exist and that the source was unchanged,
and packed the workspace (sources, `.lake` with Mathlib and the project
`.olean` files) into `ws.tar.gz`, recording its hash in `BUILD_OK`.

Each array task copied the image and the runtime to node-local `/tmp`,
unpacked the sealed workspace, checked commit, tree, clean status, Mathlib
pin and the presence of its target's `.olean`, and ran, in the same container
setting:

```
timeout -k 30s 3600s  lake env leanchecker <Module>           # task 0: default mode, all 103 targets, serial
timeout -k 30s 14400s lake env leanchecker --fresh <Module>   # task i >= 1: line i of targets-fresh.txt
```

It then checked again that the tree was unchanged and clean.

Submission (`harness/submit.sh`, record in `jobs.txt`):

```
sbatch build.sbatch                                   # --cpus-per-task=4 --mem=24G
sbatch --dependency=afterok:<build> --array=1 --cpus-per-task=2 --mem=36G task.sbatch       # pilot
sbatch --array=0,2-103%100 --cpus-per-task=2 --mem=36G task.sbatch                          # rest
```

All three with `--time=1-00:00:00 --no-requeue`. The rest was submitted once
the pilot task had printed `REPLAY_STARTED` (the gate in `submit.sh`), while
the pilot's replay was still running; the pilot later passed. The throttle
`%100` held the last three tasks (101 to 103) until earlier tasks finished;
they started at 16:18:13, 16:18:43 and 16:24:15. `--mem=36G` caps the packing
at three tasks per 128 GB node, which keeps the node-wide open-file limit
(262,144) safe (one `--fresh` run holds about 62k open files). Each task also
waited before its replay while the node's `/proc/sys/fs/file-nr` exceeded
190,000; no task had to wait (all `waited_s=0`, `PRE_REPLAY file-nr` between
1,232 and 62,320). The largest `file-nr` sample was 123,680.

The one change to the wave-L8 harness: in `submit.sh` the pilot-log lookup
`P=$(ls "$R"/tasks/001-*/task.log 2>/dev/null | head -1)` gained `|| true`,
so that `set -e` does not end `submit.sh rest` before its own "pilot has not
reached REPLAY_STARTED; wait" message when the pilot has no log yet. The
other harness files are byte-identical to those of the wave-L8 folder
(`pins.env`, `modules-all.txt`, `targets-fresh.txt` and `INPUT-SHA256SUMS`
aside, which name this commit).

Before any submission, `harness/preflight-login.sh` checked the inputs, the
container and the runtime on the login node (`harness/preflight/`;
`PREFLIGHT_OK` holds the sha256 of `INPUT-SHA256SUMS`). Its sandbox probe
(`preflight-sandbox.log`) records that unprivileged user namespaces are not
available on the login node; the jobs use the Apptainer image, not a sandbox.

`replay.py` is the script of the wave-L5 to wave-L8 replays, unchanged
(sha256 `10e90176…`). The image has no `/usr/bin/time`, so `replay.py` takes
each run's peak RSS and CPU time from `os.wait4` on that run's process. The
`.time` files show `Job: NA` because `--cleanenv` hides `SLURM_JOB_ID`; the
job id is the last column of `summary.tsv`.

## Accounting (sacct)

Per array task (104 tasks, each 2 CPUs / 36G; `sacct.tsv`):

| Tasks | Elapsed min / median / max | TotalCPU min / median / max | MaxRSS (batch) min / median / max |
|---|---|---|---|
| 103 `--fresh` (tasks 1–103) | 0:07:59 / 0:46:33 / 0:58:45 | 0:03:58 / 0:43:49 / 0:55:55 | 1,070,140 / 7,085,604 / 8,056,952 KB |
| all 104 (with task 0) | 0:07:59 / 0:46:32 / 0:58:45 | 0:03:58 / 0:43:49 / 0:55:55 | 1,070,140 / 7,085,814 / 17,211,108 KB |

sacct reports some MaxRSS values in `M` (for example `1081.50M`); they are
converted here at 1024 KB per M.

Task 0 (default mode, `5695614_0` = job 5695615): elapsed 0:24:26,
TotalCPU 0:30:03, MaxRSS 17,211,108 KB; replay phase 1,345 s for 103 targets.
Build job 5695590: elapsed 0:13:43, TotalCPU 0:31:19 on 4 CPUs / 24G,
MaxRSS 7,200,484 KB; phases `cache get` 76 s, build 449 s, tarball 201 s.
Pilot task (`5695591_1`): elapsed 0:12:36.

The `--fresh` replays themselves (`summary.tsv`, from `os.wait4`): wall
0:02:07.23 (`StratonovichHAMAudit.HermiteWordConsumer`) / median 0:41:57.68 /
0:53:33.48 (`StratonovichHAMSecondMoment.VariationalRate`); peak RSS 702,280 /
median 7,573,408 / 7,763,216 KiB (`StratonovichHAMSecondMoment.Axioms`). The
total `--fresh` wall time over the 103 runs is 209,211 s (about 58.1 h). The
rest of each task's elapsed time is the start stagger (`sleep` of
`(11 i) mod 301` s), the copy and unpacking of image, runtime and workspace,
and the checks.

Totals over the 104 tasks: elapsed 67:49:24 (135:38:48 allocated core-hours
at 2 CPUs), TotalCPU 61:51:14. One `--fresh` run uses about one core, so a
task uses about 46% of its two CPUs (median TotalCPU / (2 × Elapsed) 0.456).

The cgroup memory peak (page cache included, `monitor.log`) was 22.6 GB for
the `--fresh` tasks and 36.5 GB for task 0, out of the 36G (38.7 GB) request.

**Wall time.** Build and pilot were submitted at 2026-11-12 15:53:07 CST. The
build ran 15:53:33–16:07:16 and the pilot 16:07:17–16:19:53. The rest
(`0,2-103`) was submitted at 16:10:07; tasks 0 and 2 to 100 all started at
16:10:10, with no queue wait. The last task ended at 17:13:31.
From first submission to the last task: **1:20:24**; from the submission of
the rest: 1:03:24 (`sacct-submit.tsv`).

## Files

- `summary.tsv`: one row per `--fresh` target, in manifest order. Columns:
  module, exit code, wall time (h:mm:ss), peak RSS (KiB), output bytes, job
  id (the task's own Slurm job id).
- `fresh-time/<Module>.time`: the record of each `--fresh` run.
- `default/summary-5695615.tsv`: the default-mode replay of all 103 targets
  (task 0).
- `jobs/5695590/` (build job): `build-job.log`, `build-monitor.log`,
  `runtime-preflight.log`, `runtime-binaries.sha256`, `cache-get-1.log`,
  `BUILD_OK`, and `build.tail.log` (the last 60 lines of the build log). In
  `build-job.log` and `cache-get-1.log` the carriage returns of the
  cache-download progress line are replaced by newlines, as in the earlier
  folders.
- `jobs/<job>/` for each of the 104 counted tasks: `task.log`, `monitor.log`
  (`file-nr` and cgroup memory every 30 s) and `task.result` (bindings,
  node, start and end).
- `COLLECT.txt`: the verdict of `harness/collect.py`, run on the login node
  as `python3 -I collect.py RUN_DIR OUT_DIR`; it exited 0.
- `sacct.tsv`: the sacct query `collect.py` made (jobs and steps, with
  Elapsed, TotalCPU, ReqMem, MaxRSS, NodeList). `sacct-submit.tsv`: a second
  query, `sacct -P -X -j 5695590,5695591,5695614` with Submit, Eligible,
  Start, End, State, ExitCode, Partition, QOS and NodeList, for the wall
  time.
- `jobs.txt`: the submission record written by `submit.sh`.
- `harness/`: the inputs of the campaign, `build.sbatch`, `task.sbatch`,
  `submit.sh`, `stage-login.sh`, `preflight-login.sh`, `collect.py`,
  `replay.py`, `pins.env`, `modules-all.txt`, `targets-fresh.txt` and
  `INPUT-SHA256SUMS`, which every job checked; `make-inputs.sh`, which froze
  them on a local checkout (`make-inputs.sh <companion> 6eb79c7 OUT all`);
  `preflight/`, the login-node preflight output; `closure-check.py` with its
  output `closure-check.txt` (run locally, not part of the campaign).

The HPC username is redacted to `<user>`, the container image path to
`<container>.sif` and the runtime directory name to `<runtime-dir>` in every
file of this folder. Of the hashed inputs only `pins.env` contained them, so
its hash now differs from the one in `harness/INPUT-SHA256SUMS`;
`sha256sum -c` reports OK for the other nine files. `make-inputs.sh` is
redacted the same way and is not in `INPUT-SHA256SUMS`.
For the public release, the name of a local workstation was further replaced by `<MACHINE>` in `make-inputs.sh` and, in `d8-pilot/`, in `inputs/pilot.sbatch` and `inputs/collect.py` (comments and a printed message) and in `collect-out.txt` (that message); the hashes of `pilot.sbatch` and `collect.py` in `d8-pilot/inputs/INPUT-SHA256SUMS` are those of the originals.
