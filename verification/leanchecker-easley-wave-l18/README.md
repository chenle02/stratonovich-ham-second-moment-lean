# External kernel replay on Easley, wave L18 (`leanchecker --fresh`, array gate, 2026-11-21)

Verification evidence at 6e4644d52192: Easley leanchecker replay of wave L18 (14/14).

This is an independent replay of commit `6e4644d` on Auburn's Easley cluster
(Slurm). `6e4644d` is the wave-L18 gate commit on the integration branch
(`wave-l18/int`). It is the tenth **array** gate, with the harness of the
wave-L9 to wave-L17 gates: every harness script (`stage-login.sh`,
`preflight-login.sh`, `build.sbatch`, `task.sbatch`, `submit.sh`,
`collect.py`, `replay.py`) is byte-identical to the wave-L17 folder's, as
are `make-inputs.sh` (after redaction) and `closure-check.py`. `pins.env`,
`modules-all.txt`, `targets-fresh.txt` and `INPUT-SHA256SUMS` name this
commit.

The **thirteen new library modules** of wave L18 and the **umbrella** are
replayed `--fresh`, as at the wave-L17 gate:

```
StratonovichHAMSecondMoment
StratonovichHAMSecondMoment.EnvelopeD3Wave
StratonovichHAMSecondMoment.JointFixedOrder
StratonovichHAMSecondMoment.JointTail
StratonovichHAMSecondMoment.RieszDiagramLimits
StratonovichHAMSecondMoment.RieszDiagramLimitsHomog
StratonovichHAMSecondMoment.WickBridge
StratonovichHAMSecondMoment.WickFinal
StratonovichHAMSecondMoment.WickInterface
StratonovichHAMSecondMoment.WickMass
StratonovichHAMSecondMoment.WickMeasures
StratonovichHAMSecondMoment.WickScaling
StratonovichHAMSecondMoment.WickSpectral
StratonovichHAMSecondMoment.WickStep4
```

`targets-fresh.txt` is this list, `LC_ALL=C` sorted (made by
`make-inputs.sh ... all` and then replaced by these fourteen lines: the files
added under `StratonovichHAMSecondMoment/` between `68d0c5e` and `6e4644d`,
plus the umbrella, with `INPUT-SHA256SUMS` recomputed). Array task `i` (1 to
14) replays its line `i` with `lake env leanchecker --fresh`, which also
re-checks every transitive import (Lean core, Batteries, the imported Mathlib
slice and the project modules the target imports). The umbrella imports every
library module except `Axioms` (checked by the build job, `MANIFEST_OK
modules=189`), so its `--fresh` run re-checks those 187 library modules as
imports. Array task 0 replays all 189 manifest targets (`modules-all.txt`:
188 library modules and the umbrella) in default mode, as at every array
gate.

**Result.** All 14 `--fresh` targets exit 0 with empty output, which is the
pass signature. All 189 targets pass default-mode replay
(`default/summary-5736803.tsv`). The build job and all 15 array tasks ended
`COMPLETED 0:0`, each with one attempt; no task was resubmitted.
`collect.py` exited 0 with verdict `COMPLETE` (`COLLECT.txt`).

| Module | `--fresh` | wall | peak RSS (KiB) | default-mode wall |
|---|---|---|---|---|
| umbrella `StratonovichHAMSecondMoment` | pass | 0:43:48.75 | 7,867,864 | 0:13:44.51 |
| `EnvelopeD3Wave` | pass | 0:42:05.17 | 7,639,332 | 0:00:08.14 |
| `JointFixedOrder` | pass | 0:42:17.84 | 7,621,332 | 0:00:08.34 |
| `JointTail` | pass | 0:42:03.58 | 7,633,632 | 0:00:08.54 |
| `RieszDiagramLimits` | pass | 0:41:56.28 | 7,613,896 | 0:00:08.39 |
| `RieszDiagramLimitsHomog` | pass | 0:43:20.29 | 7,612,556 | 0:00:08.21 |
| `WickBridge` | pass | 0:43:51.25 | 7,618,200 | 0:00:08.20 |
| `WickFinal` | pass | 0:43:40.47 | 7,638,468 | 0:00:08.13 |
| `WickInterface` | pass | 0:46:13.62 | 7,618,156 | 0:00:08.24 |
| `WickMass` | pass | 0:45:47.46 | 7,626,908 | 0:00:08.20 |
| `WickMeasures` | pass | 0:44:28.59 | 7,619,100 | 0:00:08.30 |
| `WickScaling` | pass | 0:43:13.54 | 7,618,632 | 0:00:08.19 |
| `WickSpectral` | pass | 0:44:16.81 | 7,619,020 | 0:00:08.29 |
| `WickStep4` | pass | 0:46:04.94 | 7,571,568 | 0:00:08.32 |

## Coverage

`harness/closure-check.py` (unchanged since wave L5), run locally on
`68d0c5e` (the wave-L17 replay commit) against `6e4644d`, gives
(`harness/closure-check.txt`): 13 new modules (the thirteen above), 1 changed
in content (the umbrella), 0 changed only in comments, 175 byte-identical,
none removed, and one import-closure gap, `Axioms`, which imports the
umbrella. Against `8f51004` (the wave-L13/L14 replay commit, all 142 targets
`--fresh`) the same script gives 47 new modules (the thirteen above, the
fifteen of wave L17, the fifteen of wave L16 and the four of wave L15), the
umbrella changed in content, 111 comment-only, 30 byte-identical, none
removed.

So at `6e4644d` the thirteen new modules and the umbrella are replayed
`--fresh`, and the umbrella's `--fresh` run re-checks every library module
except `Axioms` as an import. `Axioms` is replayed in default mode only
(task 0). As separate `--fresh` targets, the fifteen wave-L17 modules were
replayed at `68d0c5e`, the fifteen wave-L16 modules at `ebac849`, the four
wave-L15 modules at `315a332` and the other 140 library modules at
`8f51004`; all of them are byte-identical here to `68d0c5e`, and they also
pass default mode here.

**Not covered.** The comparator-tier Lake libraries `ChallengeDefs`,
`Challenge` and `Solution` are not imported by the umbrella and are not
built by `lake build StratonovichHAMSecondMoment`. This replay does not
check them.

## What was checked

| Item | Value |
|---|---|
| Commit | `6e4644d52192a0a43c69201fac3a08a1d9d49190` |
| Tree | `a5f01fbdf23bf39583c9ae0782a84001c92c254a` (checked by the build job before and after the build, and by every task before and after its replay) |
| Toolchain | `leanprover/lean4:v4.35.0`; Lean 4.35.0 (commit `eb6cafb7290e`), Lake 5.0.0 |
| Mathlib | `56a005855ea17e0b0958f73ec801ae140b0a1679`, checked by the build job and again by every task |
| `leanchecker` binary | sha256 `12c38901cdbfab178f1bf6145dd30012e9a3b2c11ca695292a5884fa3cbaddb6` (`lean` `bf8d54e4…`, `lake` `8ba83c98…`), the same binaries as in the wave-L5 to wave-L17 replays |
| Runtime | Lean 4.35.0 runtime tarball (sha256 `9bca7d29…`), extracted on the compute node, run inside the lab Apptainer image (Ubuntu 22.04) with `--cleanenv` |
| Workspace | the build job's sealed tarball `ws.tar.gz`, 2,612,675,651 bytes, sha256 `34264966…12f8`; every counted task checked this hash before unpacking |
| Host | Easley, partition `nova_20`, QOS `resourcecap_plus`. Build and pilot on node848; tasks 0 and 2 to 14 on fourteen other nodes (node849 to node879), one per node |
| Build | `lake build StratonovichHAMSecondMoment StratonovichHAMSecondMoment.Axioms`: "Build completed successfully (9236 jobs)."; all 189 `.olean` files present |

`collect.py` binds every counted task to the build (commit, tree, inputs
hash, workspace tarball hash, `leanchecker` hash), checks that its target is
its manifest line and that its summary lists exactly that target with exit 0
and 0 output bytes (task 0: exactly the 189 manifest targets), and that
sacct shows the task `COMPLETED 0:0`.

## Commands

The private development repository was cloned on the login node over GitHub
ssh and `6e4644d…` was checked out detached (`harness/stage-login.sh`). The
login node was reached through the <MACHINE> machine's connection (from the
laptop, `ssh <MACHINE> "ssh Easley bash -s"`); the frozen inputs were sent and
the evidence fetched the same way. `harness/preflight-login.sh` (with 2 CPUs
per task) passed before any submission (`MANIFEST_OK modules=189
fresh_targets=14`; the container has git, lake, lean, leanchecker, python3,
timeout, curl, tar, gzip and sha256sum on the job's PATH; QOS headroom
224 of 1440 CPUs in use, 34 needed; output in `harness/preflight/`).

Submission (`harness/submit.sh` with `CPUS=2 MEM=48G`, record in
`jobs.txt`):

```
sbatch build.sbatch                                                          # 5736629, --cpus-per-task=4 --mem=24G
sbatch --dependency=afterok:5736629 --array=1 --cpus-per-task=2 --mem=48G task.sbatch    # pilot 5736630
sbatch --array=0,2-14%100 --cpus-per-task=2 --mem=48G task.sbatch                        # rest 5736802
```

The rest was submitted once the pilot (the umbrella) printed
`REPLAY_STARTED`. Inside the container
(`PATH=<runtime>/bin:/usr/bin:/bin`, `LEAN_NUM_THREADS=3`,
`LAKE_ARTIFACT_CACHE=false`) each task ran

```
timeout -k 30s 3600s  lake env leanchecker <Module>           # task 0: default mode, all 189 targets, serial
timeout -k 30s 14400s lake env leanchecker --fresh <Module>   # task i >= 1: line i of targets-fresh.txt
```

**Mathlib cache.** The build job's first `lake exe cache get` completed in
70 s (`CACHE attempt=1 rc=0`, `jobs/5736629/cache-get-1.log`); no retry was
needed. The build then started from no project `.olean`
(`NO_PROJECT_OLEANS_BEFORE_BUILD`).

**Open files.** No task waited for the `file-nr` guard (all `waited_s=0`,
`PRE_REPLAY file-nr` 1,240 to 1,480); the largest `file-nr` sample in the
monitors was 63,280.

## Accounting (sacct)

| Job | Role | Elapsed | TotalCPU | Alloc | MaxRSS (batch) |
|---|---|---|---|---|---|
| 5736629 | build | 0:21:29 | 1:00:16 | 4 CPU / 24G | 7,202,084 KB |
| 5736630 (`5736630_1`) | `--fresh` umbrella | 0:45:40 | 0:45:44 | 2 CPU / 48G | 7,367,064 KB |
| 5736804 (`5736802_2`) | `--fresh` `EnvelopeD3Wave` | 0:44:09 | 0:44:03 | 2 CPU / 48G | 7,765,904 KB |
| 5736805 (`5736802_3`) | `--fresh` `JointFixedOrder` | 0:44:32 | 0:44:13 | 2 CPU / 48G | 7,039,344 KB |
| 5736806 (`5736802_4`) | `--fresh` `JointTail` | 0:44:28 | 0:43:58 | 2 CPU / 48G | 7,048,724 KB |
| 5736807 (`5736802_5`) | `--fresh` `RieszDiagramLimits` | 0:44:31 | 0:43:53 | 2 CPU / 48G | 8,029,904 KB |
| 5736808 (`5736802_6`) | `--fresh` `RieszDiagramLimitsHomog` | 0:46:21 | 0:45:16 | 2 CPU / 48G | 8,056,296 KB |
| 5736809 (`5736802_7`) | `--fresh` `WickBridge` | 0:47:15 | 0:45:08 | 2 CPU / 48G | 8,080,324 KB |
| 5736810 (`5736802_8`) | `--fresh` `WickFinal` | 0:46:52 | 0:45:37 | 2 CPU / 48G | 8,100,464 KB |
| 5736811 (`5736802_9`) | `--fresh` `WickInterface` | 0:49:36 | 0:48:14 | 2 CPU / 48G | 7,103,648 KB |
| 5736812 (`5736802_10`) | `--fresh` `WickMass` | 0:49:19 | 0:47:46 | 2 CPU / 48G | 7,962,744 KB |
| 5736813 (`5736802_11`) | `--fresh` `WickMeasures` | 0:48:20 | 0:45:24 | 2 CPU / 48G | 7,983,484 KB |
| 5736814 (`5736802_12`) | `--fresh` `WickScaling` | 0:47:14 | 0:45:10 | 2 CPU / 48G | 7,090,348 KB |
| 5736815 (`5736802_13`) | `--fresh` `WickSpectral` | 0:48:34 | 0:45:20 | 2 CPU / 48G | 7,269,108 KB |
| 5736802 (`5736802_14`) | `--fresh` `WickStep4` | 0:50:26 | 0:48:10 | 2 CPU / 48G | 7,496,692 KB |
| 5736803 (`5736802_0`) | default mode, 189 targets | 0:42:14 | 0:52:22 | 2 CPU / 48G | 24,188,176 KB |

Build phases: `lake exe cache get` 70 s (one attempt), build 909 s, tarball
209 s. Task 0 replay phase 2,432 s for 189 targets (the umbrella alone
0:13:44, peak RSS 24,547,540 KiB, up from 20,943,088 KiB at the wave-L17
gate and still within the 48G allocation). Totals: 12:01:00 elapsed over the
16 jobs, TotalCPU 12:30:34.

**Wall time.** Build and pilot submitted 2026-11-21 08:52:36 CST; the rest
at 09:18:54; the last task ended at 10:09:21. From first submission to the
last task: **1:16:45**.

## Files

As in the wave-L17 folder: `summary.tsv` (one row per `--fresh` target:
module, exit, wall, peak RSS KiB, output bytes, job id), `fresh-time/`,
`default/summary-5736803.tsv`, `jobs/<job>/` (build logs and `BUILD_OK`;
per task `task.log`, `monitor.log`, `task.result`), `COLLECT.txt`,
`sacct.tsv`, `sacct-submit.tsv`, `jobs.txt`, and `harness/` (frozen inputs,
`make-inputs.sh`, `preflight/`, `closure-check.py` and `closure-check.txt`).

The HPC username is redacted to `<user>`, the container image path to
`<container>.sif` and the runtime directory name to `<runtime-dir>` in every
file of this folder. Of the hashed inputs only `pins.env` contained them, so
its hash now differs from the one in `harness/INPUT-SHA256SUMS`;
`sha256sum -c` reports OK for the other nine files. The job names
(`stratham-l11-build`, `stratham-l11-lchk`) come from the harness, which was
prepared for wave L11. No cluster lower-tier receipt was made at this commit.

For the public release, the name of a local workstation was further replaced by `<MACHINE>` in this README (the connection path to the login node) and in `make-inputs.sh` (comments only).
