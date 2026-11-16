# External kernel replay on Easley, wave L11 (`leanchecker --fresh`, array gate, 2026-11-13)

This is an independent replay of commit `b780f10` on Auburn's Easley cluster
(Slurm). `b780f10` is the merge of wave L11 into main. It is the fourth
**array** gate, with the harness of the wave-L9 and wave-L10 gates unchanged
(every harness file is byte-identical to the wave-L10 folder's; `pins.env`,
`modules-all.txt`, `targets-fresh.txt` and `INPUT-SHA256SUMS` aside, which
name this commit). One build job builds the library once from a fresh clone
and seals the workspace, and a Slurm job array then replays one target per
task, each task at 2 CPUs and 36G. Every one of the 116 targets (115 library
modules plus the umbrella) is replayed by its own
`lake env leanchecker --fresh <Module>` run, which also re-checks every
transitive import (Lean core, Batteries and the imported Mathlib slice).
Array task 0 replays all 116 targets in default mode.

**Result.** All 116 `--fresh` targets exit 0 with empty output, which is the
pass signature. All 116 targets also pass default-mode replay
(`default/summary-5697761.tsv`). The build job and all 117 array tasks ended
`COMPLETED 0:0`, each with one attempt; no task was resubmitted.

Every target was replayed `--fresh` at `b780f10`, so this folder needs no
replay-coverage argument. Every library module through wave L11 has passed a
`--fresh` replay, here at a single commit.

No cluster lower-tier receipt (`lean-pkg receipt slurm`) was made at this
commit: the two earlier ones (waves L9 and L10) agreed with the local
receipts claim by claim, which completed that stage.

## Covered modules

All 116 lines of `harness/modules-all.txt`: the 25 `StratonovichHAMAudit`
modules, the 90 `StratonovichHAMSecondMoment` modules (including `Axioms`)
and the umbrella `StratonovichHAMSecondMoment`. `harness/targets-fresh.txt`
is the same list (same sha256), and array task `i` (1 to 116) replays its
line `i`. `modules-all.txt` equals the `StratonovichHAMAudit` and
`StratonovichHAMSecondMoment` source files at `b780f10`, sorted, plus the
umbrella (checked by `harness/preflight-login.sh` on the staged clone and by
the build job, `MANIFEST_OK modules=116`).

### Import-closure check

As in waves L8 to L10, the array harness has no closure-check step: with
every target replayed `--fresh`, it is not needed for coverage. For the
record, `harness/closure-check.py` (the wave-L5 script, same sha256 as in the
wave-L5 to wave-L10 folders) was run on a local checkout relative to the
wave-L10 replay commit `b2bf7a9`. Its output is in
`harness/closure-check.txt`: 5 new modules (the wave-L11 modules
`FiniteWordCutoff`, `FockColumnBound`, `StaticInteractionCompleted`,
`TerminalWickInputs`, `TerminalWickRegularization`), 2 changed in content
(the umbrella and `Axioms`), 0 changed only in comments, 109 byte-identical,
none removed, 0 import-closure gaps.

**Not covered.** The three comparator-tier Lake libraries `ChallengeDefs`,
`Challenge` and `Solution` are not imported by the umbrella and are not built
by `lake build StratonovichHAMSecondMoment`. This replay does not check them.

## What was checked

| Item | Value |
|---|---|
| Commit | `b780f10c932e10709415939221e10c6a2a704363` |
| Tree | `b12af9bc140a05736c079087408dcdc0dcbb54e0` (checked by the build job before the build and after it, and by every task before and after its replay) |
| Library sources vs later main | **identical**: `git diff --stat b780f10 abb3479 -- 'StratonovichHAM*' lakefile.toml lake-manifest.json lean-toolchain` is empty (`abb3479`, the receipts commit, was origin/main when this folder was written) |
| Toolchain | `leanprover/lean4:v4.35.0`; Lean 4.35.0 (commit `eb6cafb7290e`), Lake 5.0.0 |
| Mathlib | `56a005855ea17e0b0958f73ec801ae140b0a1679`; the build job checked this pin after `lake exe cache get`, and every task checked it again in its unpacked workspace |
| `leanchecker` binary | sha256 `12c38901cdbfab178f1bf6145dd30012e9a3b2c11ca695292a5884fa3cbaddb6` (`lean` `bf8d54e4…`, `lake` `8ba83c98…`), the same binaries as in the wave-L5 to wave-L10 replays; every task checked its unpacked `leanchecker` and `lean` against the build job's hashes |
| Runtime | Lean 4.35.0 runtime tarball (sha256 `9bca7d29…`, checked by every job), extracted on the compute node, run inside the lab Apptainer image (Ubuntu 22.04, glibc 2.35) with `--cleanenv` |
| Workspace | the build job's sealed tarball `ws.tar.gz`, 2,541,223,792 bytes, sha256 `2ba9aba1…a99b09`; every counted task checked this hash before unpacking |
| Host | Easley, partition `nova_20`, QOS `resourcecap_plus`. Build job and pilot (task 1) on node938. The 118 jobs and tasks ran on 78 distinct nodes, at most three at a time on one node |
| Build | `lake build StratonovichHAMSecondMoment StratonovichHAMSecondMoment.Axioms`: "Build completed successfully (9163 jobs)."; `ALL_OLEANS_PRESENT=116` |

The `#print axioms` output of the `Axioms` module is not kept in full here
(only `jobs/5697758/build.tail.log`, the last 60 lines of the build log).
The lower-tier receipt at this commit reads the same build: sorry count 0,
and the 2955 claims of `claims.yaml` with only the standard axioms (2926 on
`[propext, Classical.choice, Quot.sound]`, six on `[propext, Quot.sound]`,
13 on `[propext]`, ten on none); see `.lean-receipts/b780f10c932e-*`.

`collect.py` binds every counted task to the build: the task's commit, tree,
inputs hash, workspace tarball hash and `leanchecker` hash must equal those
in `BUILD_OK`, its target must equal its manifest line, its summary must list
exactly that target with exit 0 and 0 output bytes (task 0: exactly the 116
manifest targets), and sacct must show the task `COMPLETED 0:0`. Its verdict
(`COLLECT.txt`) is `COMPLETE`: 116 of 116 `--fresh` targets counted, default
mode passed, nothing to resubmit, no problems, no failure signatures.

## Commands

The private repository was cloned on the login node over GitHub ssh, and
`b780f10c932e…` was checked out detached (`harness/stage-login.sh`). The
login node was reached through the <MACHINE> machine's connection (from the
laptop, `ssh <MACHINE> "ssh Easley bash -s"`); the frozen inputs were sent the
same way, and the evidence was fetched the same way. The build job copied
that clone, without `.lake`, to node-local `/tmp`. Inside the container, with
`PATH=<runtime>/bin:/usr/bin:/bin`, `LEAN_NUM_THREADS=3` and
`LAKE_ARTIFACT_CACHE=false`, it ran:

```
lake exe cache get
lake build StratonovichHAMSecondMoment StratonovichHAMSecondMoment.Axioms
```

checked that all 116 `.olean` files exist and that the source was unchanged,
and packed the workspace (sources, `.lake` with Mathlib and the project
`.olean` files) into `ws.tar.gz`, recording its hash in `BUILD_OK`. The
`lake exe cache get` succeeded on its first attempt (`CACHE attempt=1 rc=0`,
73 s).

Each array task copied the image and the runtime to node-local `/tmp`,
unpacked the sealed workspace, checked commit, tree, clean status, Mathlib
pin and the presence of its target's `.olean`, and ran, in the same container
setting:

```
timeout -k 30s 3600s  lake env leanchecker <Module>           # task 0: default mode, all 116 targets, serial
timeout -k 30s 14400s lake env leanchecker --fresh <Module>   # task i >= 1: line i of targets-fresh.txt
```

It then checked again that the tree was unchanged and clean.

Submission (`harness/submit.sh`, record in `jobs.txt`):

```
sbatch build.sbatch                                   # --cpus-per-task=4 --mem=24G
sbatch --dependency=afterok:<build> --array=1 --cpus-per-task=2 --mem=36G task.sbatch       # pilot
sbatch --array=0,2-116%100 --cpus-per-task=2 --mem=36G task.sbatch                          # rest
```

All three with `--time=1-00:00:00 --no-requeue`. The rest was submitted once
the pilot task had printed `REPLAY_STARTED` (the gate in `submit.sh`), while
the pilot's replay was still running; the pilot later passed. The tasks of
the rest started between 01:24:59 and 01:41:25. `--mem=36G` caps the packing
at three tasks per 128 GB node, for the node-wide open-file limit (262,144).
Each task also waited before its replay while the node's
`/proc/sys/fs/file-nr` exceeded 190,000; no task had to wait (all
`waited_s=0`, `PRE_REPLAY file-nr` between 1,440 and 123,360).

**Open files.** In this campaign one `--fresh` run held about 92k open files
at its peak (about 62k in the wave-L10 campaign). The largest `file-nr`
sample was 185,000, on node951 (job 5697873), with two replays at their peak
on one node; 99% of the 8,384 samples were at most 184,760. No sample reached
the 190,000 wait threshold or the 262,144 limit, and no task failed. Three
replays at their peak on one node would exceed the limit (about 276k); three
tasks shared a node at the same time on three nodes, without overlapping
peaks. A later campaign should cap the packing at two tasks per node (for
example `--mem=48G`) or lower the wait threshold.

Before any submission, `harness/preflight-login.sh` checked the inputs, the
container and the runtime on the login node (`harness/preflight/`;
`PREFLIGHT_OK` holds the sha256 of `INPUT-SHA256SUMS`). Its sandbox probe
(`preflight-sandbox.log`) records that unprivileged user namespaces are not
available on the login node; the jobs use the Apptainer image, not a sandbox.

`replay.py` is the script of the wave-L5 to wave-L10 replays, unchanged
(sha256 `10e90176…`). The image has no `/usr/bin/time`, so `replay.py` takes
each run's peak RSS and CPU time from `os.wait4` on that run's process. The
`.time` files show `Job: NA` because `--cleanenv` hides `SLURM_JOB_ID`; the
job id is the last column of `summary.tsv`.

## Accounting (sacct)

Per array task (117 tasks, each 2 CPUs / 36G; `sacct.tsv`):

| Tasks | Elapsed min / median / max | TotalCPU min / median / max | MaxRSS (batch) min / median / max |
|---|---|---|---|
| 116 `--fresh` (tasks 1–116) | 0:07:41 / 0:46:14 / 0:57:17 | 0:04:15 / 0:44:08 / 0:55:50 | 1,042,648 / 7,096,876 / 8,183,492 KB |
| all 117 (with task 0) | 0:07:41 / 0:46:13 / 0:57:17 | 0:04:15 / 0:44:08 / 0:55:50 | 1,042,648 / 7,099,816 / 20,609,872 KB |

sacct reports some MaxRSS values in `M`; they are converted here at 1024 KB
per M.

Task 0 (default mode, `5697760_0` = job 5697761): elapsed 0:27:37,
TotalCPU 0:33:23, MaxRSS 20,609,872 KB; replay phase 1,545 s for 116 targets.
Build job 5697758: elapsed 0:14:54, TotalCPU 0:34:56 on 4 CPUs / 24G,
MaxRSS 7,036,740 KB; phases `cache get` 73 s, build 501 s, tarball 204 s.
Pilot task (`5697759_1`): elapsed 0:13:06.

The `--fresh` replays themselves (`summary.tsv`, from `os.wait4`): wall
0:02:13.21 (`StratonovichHAMAudit.HermiteWordConsumer`) / median 0:42:10 /
0:53:26.06 (`StratonovichHAMSecondMoment.StaticInteractionCompleted`); peak
RSS 691,960 (`StratonovichHAMAudit.HermiteWord`) / median 7,577,704 /
7,759,712 KiB (`StratonovichHAMSecondMoment.Axioms`). The total `--fresh`
wall time over the 116 runs is 248,254 s (about 69.0 h). The rest of each
task's elapsed time is the start stagger (`sleep` of `(11 i) mod 301` s), the
copy and unpacking of image, runtime and workspace, and the checks.

Totals over the 117 tasks: elapsed 77:45:45 (155:31:30 allocated core-hours
at 2 CPUs), TotalCPU 73:17:56. One `--fresh` run uses about one core, so a
task uses about 47% of its two CPUs (median TotalCPU / (2 × Elapsed) 0.471).

The cgroup memory peak (page cache included, `monitor.log`) was 19.0 GB for
the `--fresh` tasks and 34.7 GB for task 0, below the 36G (38.65 GB) request.

**Wall time.** Build and pilot were submitted at 2026-11-13 01:07:06 CST. The
build ran 01:07:07–01:22:01 and the pilot 01:22:02–01:35:08. The rest
(`0,2-116`) was submitted at 01:24:58; its tasks started between 01:24:59
and 01:41:25. The last task ended at 02:33:33.
From first submission to the last task: **1:26:27**; from the submission of
the rest: 1:08:35 (`sacct-submit.tsv`).

## Files

- `summary.tsv`: one row per `--fresh` target, in manifest order. Columns:
  module, exit code, wall time (h:mm:ss), peak RSS (KiB), output bytes, job
  id (the task's own Slurm job id).
- `fresh-time/<Module>.time`: the record of each `--fresh` run.
- `default/summary-5697761.tsv`: the default-mode replay of all 116 targets
  (task 0).
- `jobs/5697758/` (build job): `build-job.log`, `build-monitor.log`,
  `runtime-preflight.log`, `runtime-binaries.sha256`, `cache-get-1.log`,
  `BUILD_OK`, and `build.tail.log` (the last 60 lines of the build log). In
  `build-job.log` and `cache-get-1.log` the carriage returns of the
  cache-download progress line are replaced by newlines, as in the earlier
  folders.
- `jobs/<job>/` for each of the 117 counted tasks: `task.log`, `monitor.log`
  (`file-nr` and cgroup memory every 30 s) and `task.result` (bindings,
  node, start and end).
- `COLLECT.txt`: the verdict of `harness/collect.py`, run on the login node
  as `python3 -I collect.py RUN_DIR OUT_DIR`; it exited 0.
- `sacct.tsv`: the sacct query `collect.py` made (jobs and steps, with
  Elapsed, TotalCPU, ReqMem, MaxRSS, NodeList). `sacct-submit.tsv`: a second
  query, `sacct -P -X -j 5697758,5697759,5697760` with Submit, Eligible,
  Start, End, State, ExitCode, Partition, QOS and NodeList, for the wall
  time.
- `jobs.txt`: the submission record written by `submit.sh`.
- `harness/`: the inputs of the campaign, `build.sbatch`, `task.sbatch`,
  `submit.sh`, `stage-login.sh`, `preflight-login.sh`, `collect.py`,
  `replay.py`, `pins.env`, `modules-all.txt`, `targets-fresh.txt` and
  `INPUT-SHA256SUMS`, which every job checked; `make-inputs.sh`, which froze
  them on a local checkout (`make-inputs.sh <companion> b780f10 OUT all`);
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
