# External kernel replay on Easley, waves L13 and L14 (`leanchecker --fresh`, array gate, 2026-11-13)

This is an independent replay of commit `8f51004` on Auburn's Easley cluster
(Slurm). `8f51004` is the merge of waves L13 and L14 into main (tags
`L13-gate` and `L14-gate`). It is the sixth **array** gate, with the harness
of the wave-L9 to wave-L12 gates. Every harness file is byte-identical to the
wave-L12 folder's (`make-inputs.sh` included, after redaction); `pins.env`,
`modules-all.txt`, `targets-fresh.txt` and `INPUT-SHA256SUMS` name this
commit. One build job builds the library once from a fresh clone and seals
the workspace, and a Slurm job array then replays one target per task, each
task at 2 CPUs and 48G (at most two tasks per node; see "Open files" below).
Every one of the 142 targets (141 library modules plus the umbrella) is
replayed by its own `lake env leanchecker --fresh <Module>` run, which also
re-checks every transitive import (Lean core, Batteries and the imported
Mathlib slice). Array task 0 replays all 142 targets in default mode.

**Result.** All 142 `--fresh` targets exit 0 with empty output, which is the
pass signature. All 142 targets also pass default-mode replay
(`default/summary-5700105.tsv`). The build job and all 143 array tasks ended
`COMPLETED 0:0`, each with one attempt; no task was resubmitted.

Every target was replayed `--fresh` at `8f51004`, so this folder needs no
replay-coverage argument. Every library module through waves L13 and L14 has
passed a `--fresh` replay, here at a single commit.

No cluster lower-tier receipt (`lean-pkg receipt slurm`) was made at this
commit, as at the wave-L11 and wave-L12 gates.

## Covered modules

All 142 lines of `harness/modules-all.txt`: the 25 `StratonovichHAMAudit`
modules, the 116 `StratonovichHAMSecondMoment` modules (including `Axioms`)
and the umbrella `StratonovichHAMSecondMoment`. `harness/targets-fresh.txt`
is the same list (same sha256), and array task `i` (1 to 142) replays its
line `i`. `modules-all.txt` equals the `StratonovichHAMAudit` and
`StratonovichHAMSecondMoment` source files at `8f51004`, sorted, plus the
umbrella (checked by `harness/preflight-login.sh` on the staged clone and by
the build job, `MANIFEST_OK modules=142`).

### Import-closure check

As in waves L8 to L12, the array harness has no closure-check step: with
every target replayed `--fresh`, it is not needed for coverage. For the
record, `harness/closure-check.py` (the wave-L5 script, same sha256 as in the
wave-L5 to wave-L12 folders) was run on a local checkout relative to the
wave-L12 replay commit `56fc59e`. Its output is in
`harness/closure-check.txt`: 22 new modules (the wave-L13 and wave-L14
modules `ClassOBridge`, `ClassOH1`, `D1Spatial`, `D1Upper`, `DiagramBridge`,
`DiagramModel`, `EndpointCorollaries`, `EndpointLemmas`, `H1Mathlib`,
`LowAlphaUpper`, `MaskedAuxiliaryReal`, `OccupationCompletion`,
`OrderTwoDiagrams`, `PhaseShiftControl`, `ResolventForm`,
`RieszFourDiagrams`, `RieszPositiveDefinite`, `SourceHeatGram`,
`TwoSimplexTime`, `VariationalMeanDerivatives`, `WhiteCollapse`,
`WhiteFour`), 2 changed in content (the umbrella and `Axioms`), 0 changed
only in comments, 118 byte-identical, none removed, 0 import-closure gaps.

**Not covered.** The three comparator-tier Lake libraries `ChallengeDefs`,
`Challenge` and `Solution` are not imported by the umbrella and are not built
by `lake build StratonovichHAMSecondMoment`. This replay does not check them.

## What was checked

| Item | Value |
|---|---|
| Commit | `8f51004c412ac618f4be6a5f4a42c7cc78188638` |
| Tree | `79a7f16872b7c49a7055b032451460e2f9af3f0d` (checked by the build job before the build and after it, and by every task before and after its replay) |
| Library sources vs later main | **identical**: `git diff --stat 8f51004 698cc61 -- 'StratonovichHAM*' lakefile.toml lake-manifest.json lean-toolchain '*.lean'` is empty (`698cc61`, the receipts commit, was origin/main when this folder was written) |
| Toolchain | `leanprover/lean4:v4.35.0`; Lean 4.35.0 (commit `eb6cafb7290e`), Lake 5.0.0 |
| Mathlib | `56a005855ea17e0b0958f73ec801ae140b0a1679`; the build job checked this pin after `lake exe cache get`, and every task checked it again in its unpacked workspace |
| `leanchecker` binary | sha256 `12c38901cdbfab178f1bf6145dd30012e9a3b2c11ca695292a5884fa3cbaddb6` (`lean` `bf8d54e4…`, `lake` `8ba83c98…`), the same binaries as in the wave-L5 to wave-L12 replays; every task checked its unpacked `leanchecker` and `lean` against the build job's hashes |
| Runtime | Lean 4.35.0 runtime tarball (sha256 `9bca7d29…`, checked by every job), extracted on the compute node, run inside the lab Apptainer image (Ubuntu 22.04, glibc 2.35) with `--cleanenv` |
| Workspace | the build job's sealed tarball `ws.tar.gz`, 2,570,720,060 bytes, sha256 `83fa0b88…b7fed9`; every counted task checked this hash before unpacking |
| Host | Easley, partition `nova_20`, QOS `resourcecap_plus`. Build job on node882, pilot (task 1) on node855. The 144 jobs and tasks ran on 94 distinct nodes, at most two tasks at a time on one node |
| Build | `lake build StratonovichHAMSecondMoment StratonovichHAMSecondMoment.Axioms`: "Build completed successfully (9189 jobs)."; `ALL_OLEANS_PRESENT=142` |

The `#print axioms` output of the `Axioms` module is not kept in full here
(only `jobs/5700029/build.tail.log`, the last 60 lines of the build log).
The lower-tier receipt at this commit reads the same commit: sorry count 0,
and the 4504 claims of `claims.yaml` with only the standard axioms
(`Classical.choice`, `Quot.sound`, `propext`); see
`.lean-receipts/8f51004c412a-*`.

`collect.py` binds every counted task to the build: the task's commit, tree,
inputs hash, workspace tarball hash and `leanchecker` hash must equal those
in `BUILD_OK`, its target must equal its manifest line, its summary must list
exactly that target with exit 0 and 0 output bytes (task 0: exactly the 142
manifest targets), and sacct must show the task `COMPLETED 0:0`. Its verdict
(`COLLECT.txt`) is `COMPLETE`: 142 of 142 `--fresh` targets counted, default
mode passed, nothing to resubmit, no problems, no failure signatures.

## Commands

The private development repository was cloned on the login node over GitHub
ssh, and `8f51004c412a…` was checked out detached
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

checked that all 142 `.olean` files exist and that the source was unchanged,
and packed the workspace (sources, `.lake` with Mathlib and the project
`.olean` files) into `ws.tar.gz`, recording its hash in `BUILD_OK`. The
`lake exe cache get` succeeded on its first attempt (`CACHE attempt=1 rc=0`,
112 s).

Each array task copied the image and the runtime to node-local `/tmp`,
unpacked the sealed workspace, checked commit, tree, clean status, Mathlib
pin and the presence of its target's `.olean`, and ran, in the same container
setting:

```
timeout -k 30s 3600s  lake env leanchecker <Module>           # task 0: default mode, all 142 targets, serial
timeout -k 30s 14400s lake env leanchecker --fresh <Module>   # task i >= 1: line i of targets-fresh.txt
```

It then checked again that the tree was unchanged and clean.

Submission (`harness/submit.sh` with `CPUS=2 MEM=48G` in its environment,
record in `jobs.txt`):

```
sbatch build.sbatch                                   # --cpus-per-task=4 --mem=24G
sbatch --dependency=afterok:<build> --array=1 --cpus-per-task=2 --mem=48G task.sbatch       # pilot
sbatch --array=0,2-142%100 --cpus-per-task=2 --mem=48G task.sbatch                          # rest
```

All three with `--time=1-00:00:00 --no-requeue`. The rest was submitted once
the pilot task had printed `REPLAY_STARTED` (the gate in `submit.sh`), while
the pilot's replay was still running; the pilot later passed. With the
throttle of 100, the tasks of the rest started between 14:40:37 and
15:26:07.

**Open files.** As at the wave-L12 gate, the packing was capped at **two
tasks per node** by the memory request alone: `--mem=48G` (49,152 MB) per
task, and a `nova_20` node has `RealMemory` 128,238 MB, so a third task does
not fit. In the sacct record no node ran more than two of these tasks at once
(nine nodes ran two at once). Each task also waited before its replay while
the node's `/proc/sys/fs/file-nr` exceeded 190,000; no task had to wait (all
`waited_s=0`, `PRE_REPLAY file-nr` between 1,240 and 62,400). The largest of
the 10,597 `file-nr` samples (`monitor.log`, every 30 s) was 123,640 (job
5700233); 99% were at most 123,360. No sample reached the 190,000 wait
threshold, and no task failed.

Before any submission, `harness/preflight-login.sh` checked the inputs, the
container and the runtime on the login node (`harness/preflight/`;
`PREFLIGHT_OK` holds the sha256 of `INPUT-SHA256SUMS`). Its sandbox probe
(`preflight-sandbox.log`) records that unprivileged user namespaces are not
available on the login node; the jobs use the Apptainer image, not a sandbox.

`replay.py` is the script of the wave-L5 to wave-L12 replays, unchanged
(sha256 `10e90176…`). The image has no `/usr/bin/time`, so `replay.py` takes
each run's peak RSS and CPU time from `os.wait4` on that run's process. The
`.time` files show `Job: NA` because `--cleanenv` hides `SLURM_JOB_ID`; the
job id is the last column of `summary.tsv`.

## Accounting (sacct)

Per array task (143 tasks, each 2 CPUs / 48G; `sacct.tsv`):

| Tasks | Elapsed min / median / max | TotalCPU min / median / max | MaxRSS (batch) min / median / max |
|---|---|---|---|
| 142 `--fresh` (tasks 1–142) | 0:06:00 / 0:46:06 / 1:02:01 | 0:04:05 / 0:44:01 / 0:59:07 | 1,044,048 / 7,119,064 / 8,300,952 KB |
| all 143 (with task 0) | 0:06:00 / 0:46:05 / 1:02:01 | 0:04:05 / 0:44:01 / 0:59:07 | 1,044,048 / 7,119,296 / 22,586,596 KB |

sacct reports some MaxRSS values in `M`; they are converted here at 1024 KB
per M.

Task 0 (default mode, `5700104_0` = job 5700105): elapsed 0:39:55,
TotalCPU 0:43:16, MaxRSS 22,586,596 KB; replay phase 2,237 s for 142
targets. Build job 5700029: elapsed 0:36:45, TotalCPU 0:46:08 on 4 CPUs /
24G, MaxRSS 8,199,512 KB; phases `cache get` 112 s, build 668 s, tarball
201 s. Pilot task (`5700030_1`): elapsed 0:13:13.

The `--fresh` replays themselves (`summary.tsv`, from `os.wait4`): wall
0:02:10 (`StratonovichHAMAudit.HermiteWordConsumer`) / median 0:42:08 /
0:56:39 (`StratonovichHAMSecondMoment.VariationalDilation`); peak RSS
691,720 (`StratonovichHAMAudit.HermiteWordConsumer`) / median 7,577,864 /
7,820,448 KiB (`StratonovichHAMSecondMoment.Axioms`). The total `--fresh`
wall time over the 142 runs is 313,573 s (about 87.1 h). The rest of each
task's elapsed time is the start stagger, the copy and unpacking of image,
runtime and workspace, and the checks.

Totals over the 143 tasks: elapsed 98:10:00 (196:20:00 allocated
core-hours at 2 CPUs), TotalCPU 92:08:35. One `--fresh` run uses about one
core, so a task uses about 47% of its two CPUs (median TotalCPU /
(2 × Elapsed) 0.468).

The cgroup memory peak (page cache included, `monitor.log`) was 19.2 GB for
the `--fresh` tasks and 37.6 GB for task 0, below the 48G (51.5 GB) request.
The larger request was for packing, not for memory.

**Wall time.** Build and pilot were submitted at 2026-11-13 14:00:37 CST. The
build ran 14:00:40–14:37:25 and the pilot 14:37:35–14:50:48. The rest
(`0,2-142`) was submitted at 14:40:28; its tasks started between 14:40:37
and 15:26:07. The last task ended at 16:14:21.
From first submission to the last task: **2:13:44**; from the submission of
the rest: 1:33:53 (`sacct-submit.tsv`).

## Files

- `summary.tsv`: one row per `--fresh` target, in manifest order. Columns:
  module, exit code, wall time (h:mm:ss), peak RSS (KiB), output bytes, job
  id (the task's own Slurm job id).
- `fresh-time/<Module>.time`: the record of each `--fresh` run.
- `default/summary-5700105.tsv`: the default-mode replay of all 142 targets
  (task 0).
- `jobs/5700029/` (build job): `build-job.log`, `build-monitor.log`,
  `runtime-preflight.log`, `runtime-binaries.sha256`, `cache-get-1.log`,
  `BUILD_OK`, and `build.tail.log` (the last 60 lines of the build log). In
  `build-job.log` and `cache-get-1.log` the carriage returns of the
  cache-download progress line are replaced by newlines, as in the earlier
  folders.
- `jobs/<job>/` for each of the 143 counted tasks: `task.log`, `monitor.log`
  (`file-nr` and cgroup memory every 30 s) and `task.result` (bindings,
  node, start and end).
- `COLLECT.txt`: the verdict of `harness/collect.py`, run on the login node
  as `python3 -I collect.py RUN_DIR OUT_DIR`; it exited 0.
- `sacct.tsv`: the sacct query `collect.py` made (jobs and steps, with
  Elapsed, TotalCPU, ReqMem, MaxRSS, NodeList). `sacct-submit.tsv`: a second
  query, `sacct -P -X -j 5700029,5700030,5700104` with Submit, Eligible,
  Start, End, State, ExitCode, Partition, QOS and NodeList, for the wall
  time.
- `jobs.txt`: the submission record written by `submit.sh`.
- `harness/`: the inputs of the campaign, `build.sbatch`, `task.sbatch`,
  `submit.sh`, `stage-login.sh`, `preflight-login.sh`, `collect.py`,
  `replay.py`, `pins.env`, `modules-all.txt`, `targets-fresh.txt` and
  `INPUT-SHA256SUMS`, which every job checked; `make-inputs.sh`, which froze
  them on a local checkout (`make-inputs.sh <companion> 8f51004 OUT all`);
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
