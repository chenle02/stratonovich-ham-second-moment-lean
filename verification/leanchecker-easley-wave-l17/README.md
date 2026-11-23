# External kernel replay on Easley, wave L17 (`leanchecker --fresh`, array gate, 2026-11-20)

Verification evidence at 68d0c5e6fd03: Easley leanchecker replay of wave L17 (16/16).

This is an independent replay of commit `68d0c5e` on Auburn's Easley cluster
(Slurm). `68d0c5e` is the wave-L17 gate commit on the integration branch
(`wave-l17/int`). It is the ninth **array** gate, with the harness of the
wave-L9 to wave-L16 gates: every harness script (`stage-login.sh`,
`preflight-login.sh`, `build.sbatch`, `task.sbatch`, `submit.sh`,
`collect.py`, `replay.py`) is byte-identical to the wave-L16 folder's, as
are `make-inputs.sh` (after redaction) and `closure-check.py`. `pins.env`,
`modules-all.txt`, `targets-fresh.txt` and `INPUT-SHA256SUMS` name this
commit.

The **fifteen new library modules** of wave L17 and the **umbrella** are
replayed `--fresh`, as at the wave-L16 gate:

```
StratonovichHAMSecondMoment
StratonovichHAMSecondMoment.CrudeCorrected
StratonovichHAMSecondMoment.EnvelopeD3
StratonovichHAMSecondMoment.EnvelopeD3Final
StratonovichHAMSecondMoment.EnvelopeFinal
StratonovichHAMSecondMoment.GreenSmoothed3
StratonovichHAMSecondMoment.HomogeneousEnvelope
StratonovichHAMSecondMoment.PairingBridge
StratonovichHAMSecondMoment.PairingCapRemoval
StratonovichHAMSecondMoment.PairingConvolution
StratonovichHAMSecondMoment.PairingDampedNorms
StratonovichHAMSecondMoment.PairingEnvelope
StratonovichHAMSecondMoment.PairingInterface
StratonovichHAMSecondMoment.PairingRegional
StratonovichHAMSecondMoment.PairingSmoothedNorms
StratonovichHAMSecondMoment.PairingTranslatedCS
```

`targets-fresh.txt` is this list, `LC_ALL=C` sorted (made by
`make-inputs.sh ... all` and then replaced by these sixteen lines: the files
added under `StratonovichHAMSecondMoment/` between `ebac849` and `68d0c5e`,
plus the umbrella, with `INPUT-SHA256SUMS` recomputed). Array task `i` (1 to
16) replays its line `i` with `lake env leanchecker --fresh`, which also
re-checks every transitive import (Lean core, Batteries, the imported Mathlib
slice and the project modules the target imports). The umbrella imports every
library module except `Axioms` (checked by the build job, `MANIFEST_OK
modules=176`), so its `--fresh` run re-checks those 174 library modules as
imports. Array task 0 replays all 176 manifest targets (`modules-all.txt`:
175 library modules and the umbrella) in default mode, as at every array
gate.

**Result.** All 16 `--fresh` targets exit 0 with empty output, which is the
pass signature. All 176 targets pass default-mode replay
(`default/summary-5734702.tsv`). The build job and all 17 array tasks ended
`COMPLETED 0:0`, each with one attempt; no task was resubmitted.
`collect.py` exited 0 with verdict `COMPLETE` (`COLLECT.txt`).

| Module | `--fresh` | wall | peak RSS (KiB) | default-mode wall |
|---|---|---|---|---|
| umbrella `StratonovichHAMSecondMoment` | pass | 0:48:55.25 | 7,842,876 | 0:15:27.19 |
| `CrudeCorrected` | pass | 0:45:30.70 | 7,619,972 | 0:00:08.86 |
| `EnvelopeD3` | pass | 0:42:28.84 | 7,620,960 | 0:00:08.61 |
| `EnvelopeD3Final` | pass | 0:44:00.55 | 7,629,912 | 0:00:08.59 |
| `EnvelopeFinal` | pass | 0:43:23.38 | 7,627,680 | 0:00:08.62 |
| `GreenSmoothed3` | pass | 0:43:48.62 | 7,616,584 | 0:00:08.71 |
| `HomogeneousEnvelope` | pass | 0:42:35.49 | 7,619,764 | 0:00:09.01 |
| `PairingBridge` | pass | 0:42:56.32 | 7,615,512 | 0:00:09.12 |
| `PairingCapRemoval` | pass | 0:43:14.56 | 7,586,468 | 0:00:08.61 |
| `PairingConvolution` | pass | 0:42:45.18 | 7,586,212 | 0:00:09.24 |
| `PairingDampedNorms` | pass | 0:43:01.76 | 7,616,304 | 0:00:09.19 |
| `PairingEnvelope` | pass | 0:42:39.31 | 7,589,848 | 0:00:08.91 |
| `PairingInterface` | pass | 0:42:24.83 | 7,585,496 | 0:00:08.93 |
| `PairingRegional` | pass | 0:43:23.31 | 7,586,616 | 0:00:09.13 |
| `PairingSmoothedNorms` | pass | 0:42:31.23 | 7,616,620 | 0:00:09.10 |
| `PairingTranslatedCS` | pass | 0:43:15.00 | 7,586,292 | 0:00:09.23 |

## Coverage

`harness/closure-check.py` (unchanged since wave L5), run locally on
`ebac849` (the wave-L16 replay commit) against `68d0c5e`, gives
(`harness/closure-check.txt`): 15 new modules (the fifteen above), 1 changed
in content (the umbrella), 0 changed only in comments, 160 byte-identical,
none removed, and one import-closure gap, `Axioms`, which imports the
umbrella. Against `8f51004` (the wave-L13/L14 replay commit, all 142 targets
`--fresh`) the same script gives 34 new modules (the fifteen above, the
fifteen of wave L16 and the four of wave L15), the umbrella changed in
content, 111 comment-only, 30 byte-identical, none removed, and the same
single gap.

So at `68d0c5e` the fifteen new modules and the umbrella are replayed
`--fresh`, and the umbrella's `--fresh` run re-checks every library module
except `Axioms` as an import. `Axioms` is replayed in default mode only
(task 0). As separate `--fresh` targets, the fifteen wave-L16 modules were
replayed at `ebac849`, the four wave-L15 modules at `315a332` and the other
140 library modules at `8f51004`; all of them are byte-identical here to
`ebac849`, and they also pass default mode here.

**Not covered.** The comparator-tier Lake libraries `ChallengeDefs`,
`Challenge` and `Solution` are not imported by the umbrella and are not
built by `lake build StratonovichHAMSecondMoment`. This replay does not
check them.

## What was checked

| Item | Value |
|---|---|
| Commit | `68d0c5e6fd03b0dcb925e637152db199682ce18b` |
| Tree | `9ae2829d6e18d02c219c3c9dfa7eaa13ffffde4e` (checked by the build job before and after the build, and by every task before and after its replay) |
| Toolchain | `leanprover/lean4:v4.35.0`; Lean 4.35.0 (commit `eb6cafb7290e`), Lake 5.0.0 |
| Mathlib | `56a005855ea17e0b0958f73ec801ae140b0a1679`, checked by the build job and again by every task |
| `leanchecker` binary | sha256 `12c38901cdbfab178f1bf6145dd30012e9a3b2c11ca695292a5884fa3cbaddb6` (`lean` `bf8d54e4…`, `lake` `8ba83c98…`), the same binaries as in the wave-L5 to wave-L16 replays |
| Runtime | Lean 4.35.0 runtime tarball (sha256 `9bca7d29…`), extracted on the compute node, run inside the lab Apptainer image (Ubuntu 22.04) with `--cleanenv` |
| Workspace | the build job's sealed tarball `ws.tar.gz`, 2,605,167,508 bytes, sha256 `7d0943da…4368c3`; every counted task checked this hash before unpacking |
| Host | Easley, partition `nova_20`, QOS `resourcecap_plus`. Build and pilot on node873; tasks 0 and 2 to 16 on sixteen other nodes (node879 to node979), one per node |
| Build | `lake build StratonovichHAMSecondMoment StratonovichHAMSecondMoment.Axioms`: "Build completed successfully (9223 jobs)."; all 176 `.olean` files present |

`collect.py` binds every counted task to the build (commit, tree, inputs
hash, workspace tarball hash, `leanchecker` hash), checks that its target is
its manifest line and that its summary lists exactly that target with exit 0
and 0 output bytes (task 0: exactly the 176 manifest targets), and that
sacct shows the task `COMPLETED 0:0`.

## Commands

The private development repository was cloned on the login node over GitHub
ssh and `68d0c5e…` was checked out detached (`harness/stage-login.sh`). The
login node was reached through the <MACHINE> machine's connection (from the
laptop, `ssh <MACHINE> "ssh Easley bash -s"`); the frozen inputs were sent and
the evidence fetched the same way. `harness/preflight-login.sh` (with 2 CPUs
per task) passed before any submission (`MANIFEST_OK modules=176
fresh_targets=16`; the container has git, lake, lean, leanchecker, python3,
timeout, curl, tar, gzip and sha256sum on the job's PATH; QOS headroom
230 of 1440 CPUs in use, 38 needed; output in `harness/preflight/`).

Submission (`harness/submit.sh` with `CPUS=2 MEM=48G`, record in
`jobs.txt`):

```
sbatch build.sbatch                                                          # 5734650, --cpus-per-task=4 --mem=24G
sbatch --dependency=afterok:5734650 --array=1 --cpus-per-task=2 --mem=48G task.sbatch    # pilot 5734651
sbatch --array=0,2-16%100 --cpus-per-task=2 --mem=48G task.sbatch                        # rest 5734701
```

The rest was submitted once the pilot (the umbrella) printed
`REPLAY_STARTED`. Inside the container
(`PATH=<runtime>/bin:/usr/bin:/bin`, `LEAN_NUM_THREADS=3`,
`LAKE_ARTIFACT_CACHE=false`) each task ran

```
timeout -k 30s 3600s  lake env leanchecker <Module>           # task 0: default mode, all 176 targets, serial
timeout -k 30s 14400s lake env leanchecker --fresh <Module>   # task i >= 1: line i of targets-fresh.txt
```

**Mathlib cache.** The build job's first `lake exe cache get` hit its
1200 s bound (`CACHE attempt=1 rc=124`; the download had reached 8980 of
9031 files, `jobs/5734650/cache-get-1.log`). The harness's bounded second
attempt completed in 8.7 s, downloading the remaining 45 files
(`cache-get-2.log`, copied from the run directory; `collect.py` copies only
the first attempt's log). The build then started from no project `.olean`
(`NO_PROJECT_OLEANS_BEFORE_BUILD`). This retry is the harness's designed
path, not a failed job.

**Open files.** No task waited for the `file-nr` guard (all `waited_s=0`,
`PRE_REPLAY file-nr` 1,560 to 1,840); the largest `file-nr` sample in the
monitors was 63,600.

## Accounting (sacct)

| Job | Role | Elapsed | TotalCPU | Alloc | MaxRSS (batch) |
|---|---|---|---|---|---|
| 5734650 | build | 0:41:29 | 0:59:02 | 4 CPU / 24G | 7,521,964 KB |
| 5734651 (`5734651_1`) | `--fresh` umbrella | 0:50:53 | 0:50:59 | 2 CPU / 48G | 8,209,684 KB |
| 5734703 (`5734701_2`) | `--fresh` `CrudeCorrected` | 0:47:43 | 0:47:35 | 2 CPU / 48G | 7,585,932 KB |
| 5734704 (`5734701_3`) | `--fresh` `EnvelopeD3` | 0:44:50 | 0:44:30 | 2 CPU / 48G | 7,230,800 KB |
| 5734705 (`5734701_4`) | `--fresh` `EnvelopeD3Final` | 0:46:30 | 0:46:03 | 2 CPU / 48G | 7,991,624 KB |
| 5734706 (`5734701_5`) | `--fresh` `EnvelopeFinal` | 0:46:05 | 0:45:25 | 2 CPU / 48G | 7,085,540 KB |
| 5734707 (`5734701_6`) | `--fresh` `GreenSmoothed3` | 0:46:41 | 0:45:49 | 2 CPU / 48G | 7,130,436 KB |
| 5734708 (`5734701_7`) | `--fresh` `HomogeneousEnvelope` | 0:45:40 | 0:44:36 | 2 CPU / 48G | 7,894,812 KB |
| 5734709 (`5734701_8`) | `--fresh` `PairingBridge` | 0:46:19 | 0:44:57 | 2 CPU / 48G | 7,741,040 KB |
| 5734710 (`5734701_9`) | `--fresh` `PairingCapRemoval` | 0:46:45 | 0:45:15 | 2 CPU / 48G | 7,612,880 KB |
| 5734711 (`5734701_10`) | `--fresh` `PairingConvolution` | 0:46:21 | 0:44:46 | 2 CPU / 48G | 7,500,016 KB |
| 5734712 (`5734701_11`) | `--fresh` `PairingDampedNorms` | 0:46:50 | 0:45:02 | 2 CPU / 48G | 7,690,952 KB |
| 5734713 (`5734701_12`) | `--fresh` `PairingEnvelope` | 0:46:39 | 0:44:40 | 2 CPU / 48G | 7,833,652 KB |
| 5734714 (`5734701_13`) | `--fresh` `PairingInterface` | 0:46:38 | 0:44:25 | 2 CPU / 48G | 7,966,696 KB |
| 5734715 (`5734701_14`) | `--fresh` `PairingRegional` | 0:47:43 | 0:45:21 | 2 CPU / 48G | 7,008,228 KB |
| 5734716 (`5734701_15`) | `--fresh` `PairingSmoothedNorms` | 0:47:01 | 0:44:30 | 2 CPU / 48G | 7,113,764 KB |
| 5734701 (`5734701_16`) | `--fresh` `PairingTranslatedCS` | 0:47:58 | 0:45:16 | 2 CPU / 48G | 7,510,264 KB |
| 5734702 (`5734701_0`) | default mode, 176 targets | 0:43:52 | 0:55:34 | 2 CPU / 48G | 21,259,100 KB |

Build phases: `lake exe cache get` 1,213 s (two attempts, above), build
907 s, tarball 224 s. Task 0 replay phase 2,527 s for 176 targets (the
umbrella alone 0:15:27, peak RSS 20,943,088 KiB). Totals: 13:55:57 elapsed
over the 18 jobs, TotalCPU 14:03:56.

**Wall time.** Build and pilot submitted 2026-11-20 18:33:39 CST; the rest
at 19:46:06; the last task ended at 20:34:05. From first submission to the
last task: **2:00:26** (about 20 minutes of it the first cache attempt).

## Files

As in the wave-L16 folder: `summary.tsv` (one row per `--fresh` target:
module, exit, wall, peak RSS KiB, output bytes, job id), `fresh-time/`,
`default/summary-5734702.tsv`, `jobs/<job>/` (build logs and `BUILD_OK`, plus
`cache-get-2.log`; per task `task.log`, `monitor.log`, `task.result`),
`COLLECT.txt`, `sacct.tsv`, `sacct-submit.tsv`, `jobs.txt`, and `harness/`
(frozen inputs, `make-inputs.sh`, `preflight/`, `closure-check.py` and
`closure-check.txt`).

The HPC username is redacted to `<user>`, the container image path to
`<container>.sif` and the runtime directory name to `<runtime-dir>` in every
file of this folder. Of the hashed inputs only `pins.env` contained them, so
its hash now differs from the one in `harness/INPUT-SHA256SUMS`;
`sha256sum -c` reports OK for the other nine files. The job names
(`stratham-l11-build`, `stratham-l11-lchk`) come from the harness, which was
prepared for wave L11. No cluster lower-tier receipt was made at this commit.

For the public release, the name of a local workstation was further replaced by `<MACHINE>` in this README (the connection path to the login node) and in `make-inputs.sh` (comments only).
