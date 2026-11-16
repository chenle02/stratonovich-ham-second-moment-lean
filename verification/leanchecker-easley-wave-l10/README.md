# External kernel replay on Easley, wave L10 (`leanchecker --fresh`, array gate, 2026-11-12)

This is an independent replay of commit `b2bf7a9` on Auburn's Easley cluster
(Slurm). `b2bf7a9` is the merge of wave L10 into main. It is the third
**array** gate, with the harness of the wave-L9 gate unchanged (every
harness file is byte-identical to the wave-L9 folder's; `pins.env`,
`modules-all.txt`, `targets-fresh.txt` and `INPUT-SHA256SUMS` aside, which
name this commit). One build job builds the library once from a fresh clone
and seals the workspace, and a Slurm job array then replays one target per
task, each task at 2 CPUs and 36G. Every one of the 111 targets (110 library
modules plus the umbrella) is replayed by its own
`lake env leanchecker --fresh <Module>` run, which also re-checks every
transitive import (Lean core, Batteries and the imported Mathlib slice).
Array task 0 replays all 111 targets in default mode.

**Result.** All 111 `--fresh` targets exit 0 with empty output, which is the
pass signature. All 111 targets also pass default-mode replay
(`default/summary-5696231.tsv`). The build job and all 112 array tasks ended
`COMPLETED 0:0`, each with one attempt; no task was resubmitted.

Every target was replayed `--fresh` at `b2bf7a9`, so this folder needs no
replay-coverage argument. Every library module through wave L10 has passed a
`--fresh` replay, here at a single commit.

## Covered modules

All 111 lines of `harness/modules-all.txt`: the 25 `StratonovichHAMAudit`
modules, the 85 `StratonovichHAMSecondMoment` modules (including `Axioms`)
and the umbrella `StratonovichHAMSecondMoment`. `harness/targets-fresh.txt`
is the same list (same sha256), and array task `i` (1 to 111) replays its
line `i`. `modules-all.txt` equals the `StratonovichHAMAudit` and
`StratonovichHAMSecondMoment` source files at `b2bf7a9`, sorted, plus the
umbrella (checked by `harness/preflight-login.sh` on the staged clone and by
the build job, `MANIFEST_OK modules=111`).

### Import-closure check

As in waves L8 and L9, the array harness has no closure-check step: with
every target replayed `--fresh`, it is not needed for coverage. For the
record, `harness/closure-check.py` (the wave-L5 script, same sha256 as in the
wave-L5 to wave-L9 folders) was run on a local checkout. Its output is in
`harness/closure-check.txt`:

- relative to the wave-L9 replay commit `6eb79c7`: 8 new modules (the
  wave-L10 modules `AlphaOneConvolution`, `FixedSplit`, `FixedSplitCore`,
  `HigherRieszThree`, `HigherRieszTwo`, `L10Completed`, `WhiteModel`,
  `WhiteMomentBounds`), 2 changed in content (the umbrella and `Axioms`),
  0 changed only in comments, 101 byte-identical, none removed, 0
  import-closure gaps;
- relative to `c622c25` (origin/main when this folder was written): all 111
  modules byte-identical, none new or removed.

**Not covered.** The three comparator-tier Lake libraries `ChallengeDefs`,
`Challenge` and `Solution` are not imported by the umbrella and are not built
by `lake build StratonovichHAMSecondMoment`. This replay does not check them.

## What was checked

| Item | Value |
|---|---|
| Commit | `b2bf7a921fb8cbae1dcd58fb5c6331019989c4c0` |
| Tree | `50c3c6e777301316f3daf058456ce257590898c6` (checked by the build job before the build and after it, and by every task before and after its replay) |
| Library sources vs later main | **identical**: `git diff --stat b2bf7a9 c622c25 -- 'StratonovichHAM*' lakefile.toml lake-manifest.json lean-toolchain` is empty (`c622c25` was origin/main when this folder was written) |
| Toolchain | `leanprover/lean4:v4.35.0`; Lean 4.35.0 (commit `eb6cafb7290e`), Lake 5.0.0 |
| Mathlib | `56a005855ea17e0b0958f73ec801ae140b0a1679`; the build job checked this pin after `lake exe cache get`, and every task checked it again in its unpacked workspace |
| `leanchecker` binary | sha256 `12c38901cdbfab178f1bf6145dd30012e9a3b2c11ca695292a5884fa3cbaddb6` (`lean` `bf8d54e4…`, `lake` `8ba83c98…`), the same binaries as in the wave-L5 to wave-L9 replays; every task checked its unpacked `leanchecker` and `lean` against the build job's hashes |
| Runtime | Lean 4.35.0 runtime tarball (sha256 `9bca7d29…`, checked by every job), extracted on the compute node, run inside the lab Apptainer image (Ubuntu 22.04, glibc 2.35) with `--cleanenv` |
| Workspace | the build job's sealed tarball `ws.tar.gz`, 2,535,610,422 bytes, sha256 `98b091e3…0a886e`; every counted task checked this hash before unpacking |
| Host | Easley, partition `nova_20`, QOS `resourcecap_plus`. Build job on node831; the pilot (task 1) and one other task also ran on node831. The 112 tasks ran on 101 distinct nodes, at most two per node |
| Build | `lake build StratonovichHAMSecondMoment StratonovichHAMSecondMoment.Axioms`: "Build completed successfully (9158 jobs)."; `ALL_OLEANS_PRESENT=111` |

The `#print axioms` output of the `Axioms` module is not kept in full here
(only `jobs/5696224/build.tail.log`, the last 60 lines of the build log).
The lower-tier receipts at this commit read the same build: 2988
`#print axioms` results, sorry count 0, and the 2757 claims of
`claims.yaml` with only the standard axioms (2736 on
`[propext, Classical.choice, Quot.sound]`, four on `[propext, Quot.sound]`,
13 on `[propext]`, four on none); see `.lean-receipts/b2bf7a921fb8-*` and
`verification/slurm-receipt-pilot-wave-l10/`.

`collect.py` binds every counted task to the build: the task's commit, tree,
inputs hash, workspace tarball hash and `leanchecker` hash must equal those
in `BUILD_OK`, its target must equal its manifest line, its summary must list
exactly that target with exit 0 and 0 output bytes (task 0: exactly the 111
manifest targets), and sacct must show the task `COMPLETED 0:0`. Its verdict
(`COLLECT.txt`) is `COMPLETE`: 111 of 111 `--fresh` targets counted, default
mode passed, nothing to resubmit, no problems, no failure signatures.

## Commands

The private repository was cloned on the login node over GitHub ssh, and
`b2bf7a921fb8…` was checked out detached (`harness/stage-login.sh`). The
login node was reached through the <MACHINE> machine's connection (from the
laptop, `ssh <MACHINE> "ssh Easley bash -s"`); the frozen inputs were sent the
same way. The build job copied that clone, without `.lake`, to node-local
`/tmp`. Inside the container, with `PATH=<runtime>/bin:/usr/bin:/bin`,
`LEAN_NUM_THREADS=3` and `LAKE_ARTIFACT_CACHE=false`, it ran:

```
lake exe cache get
lake build StratonovichHAMSecondMoment StratonovichHAMSecondMoment.Axioms
```

checked that all 111 `.olean` files exist and that the source was unchanged,
and packed the workspace (sources, `.lake` with Mathlib and the project
`.olean` files) into `ws.tar.gz`, recording its hash in `BUILD_OK`.

The first `lake exe cache get` attempt reached its bounded timeout (1200 s,
`CACHE attempt=1 rc=124`, with 8972 of 9031 files downloaded; the download
rate from the Mathlib cache was low); the harness's second attempt completed
in seconds (`CACHE attempt=2 rc=0`, `jobs/5696224/cache-get-2.log`), and the
Mathlib pin was then checked (`MATHLIB_PIN_OK`). This retry is the harness's
designed behaviour (at most three attempts); it is the reason the build job
took 0:33:05 instead of about 0:14.

Each array task copied the image and the runtime to node-local `/tmp`,
unpacked the sealed workspace, checked commit, tree, clean status, Mathlib
pin and the presence of its target's `.olean`, and ran, in the same container
setting:

```
timeout -k 30s 3600s  lake env leanchecker <Module>           # task 0: default mode, all 111 targets, serial
timeout -k 30s 14400s lake env leanchecker --fresh <Module>   # task i >= 1: line i of targets-fresh.txt
```

It then checked again that the tree was unchanged and clean.

Submission (`harness/submit.sh`, record in `jobs.txt`):

```
sbatch build.sbatch                                   # --cpus-per-task=4 --mem=24G
sbatch --dependency=afterok:<build> --array=1 --cpus-per-task=2 --mem=36G task.sbatch       # pilot
sbatch --array=0,2-111%100 --cpus-per-task=2 --mem=36G task.sbatch                          # rest
```

All three with `--time=1-00:00:00 --no-requeue`. The rest was submitted once
the pilot task had printed `REPLAY_STARTED` (the gate in `submit.sh`), while
the pilot's replay was still running; the pilot later passed. The tasks of
the rest started between 20:30:29 and 20:45:15. `--mem=36G` caps the packing
at three tasks per 128 GB node, which keeps the node-wide open-file limit
(262,144) safe (one `--fresh` run holds about 62k open files). Each task also
waited before its replay while the node's `/proc/sys/fs/file-nr` exceeded
190,000; no task had to wait (all `waited_s=0`, `PRE_REPLAY file-nr` between
1,240 and 1,568). The largest `file-nr` sample was 62,880.

Before any submission, `harness/preflight-login.sh` checked the inputs, the
container and the runtime on the login node (`harness/preflight/`;
`PREFLIGHT_OK` holds the sha256 of `INPUT-SHA256SUMS`). Its sandbox probe
(`preflight-sandbox.log`) records that unprivileged user namespaces are not
available on the login node; the jobs use the Apptainer image, not a sandbox.

`replay.py` is the script of the wave-L5 to wave-L9 replays, unchanged
(sha256 `10e90176…`). The image has no `/usr/bin/time`, so `replay.py` takes
each run's peak RSS and CPU time from `os.wait4` on that run's process. The
`.time` files show `Job: NA` because `--cleanenv` hides `SLURM_JOB_ID`; the
job id is the last column of `summary.tsv`.

## Accounting (sacct)

Per array task (112 tasks, each 2 CPUs / 36G; `sacct.tsv`):

| Tasks | Elapsed min / median / max | TotalCPU min / median / max | MaxRSS (batch) min / median / max |
|---|---|---|---|
| 111 `--fresh` (tasks 1–111) | 0:06:19 / 0:45:48 / 0:57:43 | 0:04:00 / 0:43:42 / 0:55:11 | 1,053,192 / 7,076,252 / 8,102,144 KB |
| all 112 (with task 0) | 0:06:19 / 0:45:48 / 0:57:43 | 0:04:00 / 0:43:40 / 0:55:11 | 1,053,192 / 7,077,918 / 23,878,612 KB |

sacct reports some MaxRSS values in `M`; they are converted here at 1024 KB
per M.

Task 0 (default mode, `5696230_0` = job 5696231): elapsed 0:23:39,
TotalCPU 0:27:59, MaxRSS 23,878,612 KB; replay phase 1,299 s for 111 targets.
Build job 5696224: elapsed 0:33:05, TotalCPU 0:34:11 on 4 CPUs / 24G,
MaxRSS 7,163,924 KB; phases `cache get` 1,206 s (two attempts, see Commands),
build 496 s, tarball 201 s. Pilot task (`5696225_1`): elapsed 0:13:22.

The `--fresh` replays themselves (`summary.tsv`, from `os.wait4`): wall
0:02:08.05 (`StratonovichHAMAudit.HermiteWord`) / median 0:41:50 /
0:52:51.19 (`StratonovichHAMSecondMoment.GaussianHermite`); peak RSS 691,580 /
median 7,575,428 / 7,773,444 KiB (`StratonovichHAMSecondMoment.Axioms`). The
total `--fresh` wall time over the 111 runs is 227,694 s (about 63.2 h). The
rest of each task's elapsed time is the start stagger (`sleep` of
`(11 i) mod 301` s), the copy and unpacking of image, runtime and workspace,
and the checks.

Totals over the 112 tasks: elapsed 72:03:44 (144:07:28 allocated core-hours
at 2 CPUs), TotalCPU 67:09:32. One `--fresh` run uses about one core, so a
task uses about 47% of its two CPUs (median TotalCPU / (2 × Elapsed) 0.467).

The cgroup memory peak (page cache included, `monitor.log`) was 20.4 GB for
the `--fresh` tasks and 38.7 GB for task 0, which is the whole 36G
(38.65 GB) request: task 0's resident set was 23.9 GB (sacct MaxRSS), and
the rest of its cgroup peak is page cache, which the kernel reclaims at the
limit. Task 0 was not killed and passed; a later campaign may give task 0
more memory.

**Wall time.** Build and pilot were submitted at 2026-11-12 19:54:05 CST. The
build ran 19:54:06–20:27:11 and the pilot 20:27:12–20:40:34. The rest
(`0,2-111`) was submitted at 20:30:28; its tasks started between 20:30:29
and 20:45:15. The last task ended at 21:33:35.
From first submission to the last task: **1:39:30**; from the submission of
the rest: 1:03:07 (`sacct-submit.tsv`).

## Files

- `summary.tsv`: one row per `--fresh` target, in manifest order. Columns:
  module, exit code, wall time (h:mm:ss), peak RSS (KiB), output bytes, job
  id (the task's own Slurm job id).
- `fresh-time/<Module>.time`: the record of each `--fresh` run.
- `default/summary-5696231.tsv`: the default-mode replay of all 111 targets
  (task 0).
- `jobs/5696224/` (build job): `build-job.log`, `build-monitor.log`,
  `runtime-preflight.log`, `runtime-binaries.sha256`, `cache-get-1.log`,
  `cache-get-2.log` (fetched from the run directory separately, since
  `collect.py` copies the first attempt only), `BUILD_OK`, and
  `build.tail.log` (the last 60 lines of the build log). In `build-job.log`
  and the `cache-get` logs the carriage returns of the cache-download
  progress line are replaced by newlines, as in the earlier folders.
- `jobs/<job>/` for each of the 112 counted tasks: `task.log`, `monitor.log`
  (`file-nr` and cgroup memory every 30 s) and `task.result` (bindings,
  node, start and end).
- `COLLECT.txt`: the verdict of `harness/collect.py`, run on the login node
  as `python3 -I collect.py RUN_DIR OUT_DIR`; it exited 0.
- `sacct.tsv`: the sacct query `collect.py` made (jobs and steps, with
  Elapsed, TotalCPU, ReqMem, MaxRSS, NodeList). `sacct-submit.tsv`: a second
  query, `sacct -P -X -j 5696224,5696225,5696230` with Submit, Eligible,
  Start, End, State, ExitCode, Partition, QOS and NodeList, for the wall
  time.
- `jobs.txt`: the submission record written by `submit.sh`.
- `harness/`: the inputs of the campaign, `build.sbatch`, `task.sbatch`,
  `submit.sh`, `stage-login.sh`, `preflight-login.sh`, `collect.py`,
  `replay.py`, `pins.env`, `modules-all.txt`, `targets-fresh.txt` and
  `INPUT-SHA256SUMS`, which every job checked; `make-inputs.sh`, which froze
  them on a local checkout (`make-inputs.sh <companion> b2bf7a9 OUT all`);
  `preflight/`, the login-node preflight output; `closure-check.py` with its
  output `closure-check.txt` (run locally, not part of the campaign).

The HPC username is redacted to `<user>`, the container image path to
`<container>.sif` and the runtime directory name to `<runtime-dir>` in every
file of this folder. Of the hashed inputs only `pins.env` contained them, so
its hash now differs from the one in `harness/INPUT-SHA256SUMS`;
`sha256sum -c` reports OK for the other nine files. `make-inputs.sh` is
redacted the same way and is not in `INPUT-SHA256SUMS`. The build job's name
`stratham-l11-build` comes from the harness, which was prepared for wave
L11 and is used unchanged.

For the public release, the name of a local workstation was further replaced by `<MACHINE>` in this README (the connection path to the login node) and in `make-inputs.sh` (comments only).
