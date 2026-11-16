# External kernel replay on Easley, wave L12 (`leanchecker --fresh`, array gate, 2026-11-13)

This is an independent replay of commit `56fc59e` on Auburn's Easley cluster
(Slurm). `56fc59e` is the merge of wave L12 into main. It is the fifth
**array** gate, with the harness of the wave-L9 to wave-L11 gates. Every
harness file is byte-identical to the wave-L11 folder's, except
`make-inputs.sh`, whose `GITHUB_REPO` line now names the development
repository `stratonovich-ham-second-moment-lean-dev` (the repository was
renamed after the wave-L11 gate); `pins.env`, `modules-all.txt`,
`targets-fresh.txt` and `INPUT-SHA256SUMS` name this commit. One build job
builds the library once from a fresh clone and seals the workspace, and a
Slurm job array then replays one target per task, each task at 2 CPUs and
**48G** (36G in the earlier array gates; see "Open files" below). Every one
of the 120 targets (119 library modules plus the umbrella) is replayed by its
own `lake env leanchecker --fresh <Module>` run, which also re-checks every
transitive import (Lean core, Batteries and the imported Mathlib slice).
Array task 0 replays all 120 targets in default mode.

**Result.** All 120 `--fresh` targets exit 0 with empty output, which is the
pass signature. All 120 targets also pass default-mode replay
(`default/summary-5698960.tsv`). The build job and all 121 array tasks ended
`COMPLETED 0:0`, each with one attempt; no task was resubmitted.

Every target was replayed `--fresh` at `56fc59e`, so this folder needs no
replay-coverage argument. Every library module through wave L12 has passed a
`--fresh` replay, here at a single commit.

No cluster lower-tier receipt (`lean-pkg receipt slurm`) was made at this
commit: the two earlier ones (waves L9 and L10) agreed with the local
receipts claim by claim, which completed that stage.

## Covered modules

All 120 lines of `harness/modules-all.txt`: the 25 `StratonovichHAMAudit`
modules, the 94 `StratonovichHAMSecondMoment` modules (including `Axioms`)
and the umbrella `StratonovichHAMSecondMoment`. `harness/targets-fresh.txt`
is the same list (same sha256), and array task `i` (1 to 120) replays its
line `i`. `modules-all.txt` equals the `StratonovichHAMAudit` and
`StratonovichHAMSecondMoment` source files at `56fc59e`, sorted, plus the
umbrella (checked by `harness/preflight-login.sh` on the staged clone and by
the build job, `MANIFEST_OK modules=120`).

### Import-closure check

As in waves L8 to L11, the array harness has no closure-check step: with
every target replayed `--fresh`, it is not needed for coverage. For the
record, `harness/closure-check.py` (the wave-L5 script, same sha256 as in the
wave-L5 to wave-L11 folders) was run on a local checkout relative to the
wave-L11 replay commit `b780f10`. Its output is in
`harness/closure-check.txt`: 4 new modules (the wave-L12 modules
`DampedSmoothing`, `FockSandwichModel`, `SourceTube`,
`TerminalWickComplete`), 2 changed in content (the umbrella and `Axioms`), 1
changed only in comments (`DampedMultiplier`, the wave-L12 review repair of
its doc comments), 113 byte-identical, none removed, 0 import-closure gaps.

**Not covered.** The three comparator-tier Lake libraries `ChallengeDefs`,
`Challenge` and `Solution` are not imported by the umbrella and are not built
by `lake build StratonovichHAMSecondMoment`. This replay does not check them.

## What was checked

| Item | Value |
|---|---|
| Commit | `56fc59ec31b8ede85ac5ab7a2283237b091029a7` |
| Tree | `df0322362d43b18a73c060519d72955b328900c5` (checked by the build job before the build and after it, and by every task before and after its replay) |
| Library sources vs later main | **identical**: `git diff --stat 56fc59e ed16d81 -- 'StratonovichHAM*' lakefile.toml lake-manifest.json lean-toolchain '*.lean'` is empty (`ed16d81`, the receipts commit, was origin/main when this folder was written) |
| Toolchain | `leanprover/lean4:v4.35.0`; Lean 4.35.0 (commit `eb6cafb7290e`), Lake 5.0.0 |
| Mathlib | `56a005855ea17e0b0958f73ec801ae140b0a1679`; the build job checked this pin after `lake exe cache get`, and every task checked it again in its unpacked workspace |
| `leanchecker` binary | sha256 `12c38901cdbfab178f1bf6145dd30012e9a3b2c11ca695292a5884fa3cbaddb6` (`lean` `bf8d54e4…`, `lake` `8ba83c98…`), the same binaries as in the wave-L5 to wave-L11 replays; every task checked its unpacked `leanchecker` and `lean` against the build job's hashes |
| Runtime | Lean 4.35.0 runtime tarball (sha256 `9bca7d29…`, checked by every job), extracted on the compute node, run inside the lab Apptainer image (Ubuntu 22.04, glibc 2.35) with `--cleanenv` |
| Workspace | the build job's sealed tarball `ws.tar.gz`, 2,546,791,086 bytes, sha256 `1b3937f9…7f7af2`; every counted task checked this hash before unpacking |
| Host | Easley, partition `nova_20`, QOS `resourcecap_plus`. Build job and pilot (task 1) on node832. The 122 jobs and tasks ran on 93 distinct nodes, at most two at a time on one node |
| Build | `lake build StratonovichHAMSecondMoment StratonovichHAMSecondMoment.Axioms`: "Build completed successfully (9167 jobs)."; `ALL_OLEANS_PRESENT=120` |

The `#print axioms` output of the `Axioms` module is not kept in full here
(only `jobs/5698659/build.tail.log`, the last 60 lines of the build log).
The lower-tier receipt at this commit reads the same commit: sorry count 0,
and the 3107 claims of `claims.yaml` with only the standard axioms
(`Classical.choice`, `Quot.sound`, `propext`); see
`.lean-receipts/56fc59ec31b8-*`.

`collect.py` binds every counted task to the build: the task's commit, tree,
inputs hash, workspace tarball hash and `leanchecker` hash must equal those
in `BUILD_OK`, its target must equal its manifest line, its summary must list
exactly that target with exit 0 and 0 output bytes (task 0: exactly the 120
manifest targets), and sacct must show the task `COMPLETED 0:0`. Its verdict
(`COLLECT.txt`) is `COMPLETE`: 120 of 120 `--fresh` targets counted, default
mode passed, nothing to resubmit, no problems, no failure signatures.

## Commands

The private development repository was cloned on the login node over GitHub
ssh, and `56fc59ec31b8…` was checked out detached
(`harness/stage-login.sh`). The login node was reached through the <MACHINE>
machine's connection (from the laptop, `ssh <MACHINE> "ssh Easley bash -s"`);
the frozen inputs were sent the same way, and the evidence was fetched the
same way. The build job copied that clone, without `.lake`, to node-local
`/tmp`. Inside the container, with `PATH=<runtime>/bin:/usr/bin:/bin`,
`LEAN_NUM_THREADS=3` and `LAKE_ARTIFACT_CACHE=false`, it ran:

```
lake exe cache get
lake build StratonovichHAMSecondMoment StratonovichHAMSecondMoment.Axioms
```

checked that all 120 `.olean` files exist and that the source was unchanged,
and packed the workspace (sources, `.lake` with Mathlib and the project
`.olean` files) into `ws.tar.gz`, recording its hash in `BUILD_OK`. The
`lake exe cache get` succeeded on its first attempt (`CACHE attempt=1 rc=0`,
71 s).

Each array task copied the image and the runtime to node-local `/tmp`,
unpacked the sealed workspace, checked commit, tree, clean status, Mathlib
pin and the presence of its target's `.olean`, and ran, in the same container
setting:

```
timeout -k 30s 3600s  lake env leanchecker <Module>           # task 0: default mode, all 120 targets, serial
timeout -k 30s 14400s lake env leanchecker --fresh <Module>   # task i >= 1: line i of targets-fresh.txt
```

It then checked again that the tree was unchanged and clean.

Submission (`harness/submit.sh` with `CPUS=2 MEM=48G` in its environment,
record in `jobs.txt`):

```
sbatch build.sbatch                                   # --cpus-per-task=4 --mem=24G
sbatch --dependency=afterok:<build> --array=1 --cpus-per-task=2 --mem=48G task.sbatch       # pilot
sbatch --array=0,2-120%100 --cpus-per-task=2 --mem=48G task.sbatch                          # rest
```

All three with `--time=1-00:00:00 --no-requeue`. The rest was submitted once
the pilot task had printed `REPLAY_STARTED` (the gate in `submit.sh`), while
the pilot's replay was still running; the pilot later passed. The tasks of
the rest started between 08:45:34 and 09:01:49.

**Open files.** The wave-L11 campaign recorded a `file-nr` sample of 185,000
of the node-wide limit of 262,144, with two replays at their peak on one
node, and noted that three replays at their peak on one node would exceed
the limit. This campaign therefore capped the packing at **two tasks per
node** by the memory request alone: `--mem=48G` (49,152 MB) per task, and a
`nova_20` node has `RealMemory` 128,238 MB (`sinfo`), so a third task does
not fit (3 × 49,152 = 147,456 MB), while two do (98,304 MB). The harness
files are unchanged; the request is set by `submit.sh`'s `MEM` variable. In
the sacct record no node ran more than two of these tasks at once (nine
nodes ran two at once). Each task also waited before its replay while the
node's `/proc/sys/fs/file-nr` exceeded 190,000; no task had to wait (all
`waited_s=0`, `PRE_REPLAY file-nr` between 1,240 and 62,440). The largest of
the 8,510 `file-nr` samples (`monitor.log`, every 30 s) was 123,400, on
node845 (job 5699250); 99% were at most 123,240. No sample reached the
190,000 wait threshold, and no task failed.

Before any submission, `harness/preflight-login.sh` checked the inputs, the
container and the runtime on the login node (`harness/preflight/`;
`PREFLIGHT_OK` holds the sha256 of `INPUT-SHA256SUMS`). Its sandbox probe
(`preflight-sandbox.log`) records that unprivileged user namespaces are not
available on the login node; the jobs use the Apptainer image, not a sandbox.

`replay.py` is the script of the wave-L5 to wave-L11 replays, unchanged
(sha256 `10e90176…`). The image has no `/usr/bin/time`, so `replay.py` takes
each run's peak RSS and CPU time from `os.wait4` on that run's process. The
`.time` files show `Job: NA` because `--cleanenv` hides `SLURM_JOB_ID`; the
job id is the last column of `summary.tsv`.

## Accounting (sacct)

Per array task (121 tasks, each 2 CPUs / 48G; `sacct.tsv`):

| Tasks | Elapsed min / median / max | TotalCPU min / median / max | MaxRSS (batch) min / median / max |
|---|---|---|---|
| 120 `--fresh` (tasks 1–120) | 0:06:18 / 0:46:21 / 0:57:28 | 0:03:59 / 0:43:48 / 0:55:17 | 1,050,356 / 7,099,204 / 8,213,032 KB |
| all 121 (with task 0) | 0:06:18 / 0:46:21 / 0:57:28 | 0:03:59 / 0:43:48 / 0:55:17 | 1,050,356 / 7,100,888 / 21,847,196 KB |

sacct reports some MaxRSS values in `M`; they are converted here at 1024 KB
per M.

Task 0 (default mode, `5698959_0` = job 5698960): elapsed 0:33:11,
TotalCPU 0:38:19, MaxRSS 21,847,196 KB; replay phase 1,725 s for 120
targets. Build job 5698659: elapsed 0:22:51, TotalCPU 0:39:59 on 4 CPUs /
24G, MaxRSS 7,158,848 KB; phases `cache get` 71 s, build 576 s, tarball
206 s. Pilot task (`5698660_1`): elapsed 0:12:46.

The `--fresh` replays themselves (`summary.tsv`, from `os.wait4`): wall
0:02:08 (`StratonovichHAMAudit.HermiteWord`) / median 0:41:55 / 0:52:58
(`StratonovichHAMSecondMoment.DampedSmoothing`); peak RSS 692,800
(`StratonovichHAMAudit.HermiteWordConsumer`) / median 7,576,964 / 7,782,448
KiB (`StratonovichHAMSecondMoment.Axioms`). The total `--fresh` wall time
over the 120 runs is 252,588 s (about 70.2 h). The rest of each task's
elapsed time is the start stagger (`sleep` of `(11 i) mod 301` s), the copy
and unpacking of image, runtime and workspace, and the checks.

Totals over the 121 tasks: elapsed 80:01:23 (160:02:46 allocated
core-hours at 2 CPUs), TotalCPU 74:34:42. One `--fresh` run uses about one
core, so a task uses about 47% of its two CPUs (median TotalCPU /
(2 × Elapsed) 0.470).

The cgroup memory peak (page cache included, `monitor.log`) was 19.0 GB for
the `--fresh` tasks and 37.0 GB for task 0, below the 48G (51.5 GB) request.
The larger request was for packing, not for memory.

**Wall time.** Build and pilot were submitted at 2026-11-13 08:19:10 CST. The
build ran 08:19:11–08:42:02 and the pilot 08:42:03–08:54:49. The rest
(`0,2-120`) was submitted at 08:45:33; its tasks started between 08:45:34
and 09:01:49. The last task ended at 09:49:31.
From first submission to the last task: **1:30:21**; from the submission of
the rest: 1:03:58 (`sacct-submit.tsv`).

## Files

- `summary.tsv`: one row per `--fresh` target, in manifest order. Columns:
  module, exit code, wall time (h:mm:ss), peak RSS (KiB), output bytes, job
  id (the task's own Slurm job id).
- `fresh-time/<Module>.time`: the record of each `--fresh` run.
- `default/summary-5698960.tsv`: the default-mode replay of all 120 targets
  (task 0).
- `jobs/5698659/` (build job): `build-job.log`, `build-monitor.log`,
  `runtime-preflight.log`, `runtime-binaries.sha256`, `cache-get-1.log`,
  `BUILD_OK`, and `build.tail.log` (the last 60 lines of the build log). In
  `build-job.log` and `cache-get-1.log` the carriage returns of the
  cache-download progress line are replaced by newlines, as in the earlier
  folders.
- `jobs/<job>/` for each of the 121 counted tasks: `task.log`, `monitor.log`
  (`file-nr` and cgroup memory every 30 s) and `task.result` (bindings,
  node, start and end).
- `COLLECT.txt`: the verdict of `harness/collect.py`, run on the login node
  as `python3 -I collect.py RUN_DIR OUT_DIR`; it exited 0.
- `sacct.tsv`: the sacct query `collect.py` made (jobs and steps, with
  Elapsed, TotalCPU, ReqMem, MaxRSS, NodeList). `sacct-submit.tsv`: a second
  query, `sacct -P -X -j 5698659,5698660,5698959` with Submit, Eligible,
  Start, End, State, ExitCode, Partition, QOS and NodeList, for the wall
  time.
- `jobs.txt`: the submission record written by `submit.sh`.
- `harness/`: the inputs of the campaign, `build.sbatch`, `task.sbatch`,
  `submit.sh`, `stage-login.sh`, `preflight-login.sh`, `collect.py`,
  `replay.py`, `pins.env`, `modules-all.txt`, `targets-fresh.txt` and
  `INPUT-SHA256SUMS`, which every job checked; `make-inputs.sh`, which froze
  them on a local checkout (`make-inputs.sh <companion> 56fc59e OUT all`);
  `preflight/`, the login-node preflight output; `closure-check.py` with its
  output `closure-check.txt` (run locally, not part of the campaign).

The HPC username is redacted to `<user>`, the container image path to
`<container>.sif` and the runtime directory name to `<runtime-dir>` in every
file of this folder. Of the hashed inputs only `pins.env` contained them, so
its hash now differs from the one in `harness/INPUT-SHA256SUMS`;
`sha256sum -c` reports OK for the other nine files. `make-inputs.sh` is
redacted the same way and is not in `INPUT-SHA256SUMS`. The job names
(`stratham-l11-build`, `stratham-l11-lchk`) come from the harness, which was
prepared for wave L11.

For the public release, the name of a local workstation was further replaced by `<MACHINE>` in this README (the connection path to the login node) and in `make-inputs.sh` (comments only).
