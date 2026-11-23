# External kernel replay on Easley, wave L16 (`leanchecker --fresh`, array gate, 2026-11-20)

Verification evidence at ebac849d61e5: Easley leanchecker replay of wave L16 (16/16).

This is an independent replay of commit `ebac849` on Auburn's Easley cluster
(Slurm). `ebac849` is the wave-L16 gate commit on the integration branch
(`wave-l16/int`). It is the eighth **array** gate, with the harness of the
wave-L9 to wave-L15 gates: every harness script (`stage-login.sh`,
`preflight-login.sh`, `build.sbatch`, `task.sbatch`, `submit.sh`,
`collect.py`, `replay.py`) is byte-identical to the wave-L15 folder's, as
are `make-inputs.sh` (after redaction) and `closure-check.py`. `pins.env`,
`modules-all.txt`, `targets-fresh.txt` and `INPUT-SHA256SUMS` name this
commit.

The **fifteen new library modules** of wave L16 and the **umbrella** are
replayed `--fresh` (the scope asked for this gate; the wave-L15 gate replayed
the umbrella in default mode only):

```
StratonovichHAMSecondMoment
StratonovichHAMSecondMoment.CameronFinal
StratonovichHAMSecondMoment.CameronInterface
StratonovichHAMSecondMoment.CameronProducts
StratonovichHAMSecondMoment.CameronSpatial
StratonovichHAMSecondMoment.CameronTemporalKernel
StratonovichHAMSecondMoment.CameronTemporalMap
StratonovichHAMSecondMoment.CameronTemporalSqrt
StratonovichHAMSecondMoment.CameronTemporalTarget
StratonovichHAMSecondMoment.CameronTemporalYoung
StratonovichHAMSecondMoment.CameronUMap
StratonovichHAMSecondMoment.CompactOperatorFoundation
StratonovichHAMSecondMoment.UniformMeanAssembly
StratonovichHAMSecondMoment.UniformMeanCutoff
StratonovichHAMSecondMoment.UniformMeanDischarge
StratonovichHAMSecondMoment.UniformMeanTensor
```

`targets-fresh.txt` is this list, `LC_ALL=C` sorted (made by
`make-inputs.sh ... all` and then replaced by these sixteen lines, with
`INPUT-SHA256SUMS` recomputed). Array task `i` (1 to 16) replays its line `i`
with `lake env leanchecker --fresh`, which also re-checks every transitive
import (Lean core, Batteries, the imported Mathlib slice and the project
modules the target imports). The umbrella imports every library module except
`Axioms` (checked by the build job), so its `--fresh` run re-checks those
159 library modules as imports. Array task 0 replays all 161 manifest targets (`modules-all.txt`:
160 library modules and the umbrella) in default mode, as at every array
gate.

**Result.** All 16 `--fresh` targets exit 0 with empty output, which is the
pass signature. All 161 targets pass default-mode replay
(`default/summary-5733117.tsv`). The build job and all 17 array tasks ended
`COMPLETED 0:0`, each with one attempt; no task was resubmitted.
`collect.py` exited 0 with verdict `COMPLETE` (`COLLECT.txt`).

| Module | `--fresh` | wall | peak RSS (KiB) | default-mode wall |
|---|---|---|---|---|
| umbrella `StratonovichHAMSecondMoment` | pass | 0:44:02.24 | 7,842,756 | 0:11:20.24 |
| `CameronFinal` | pass | 0:43:57.46 | 7,635,468 | 0:00:08.06 |
| `CameronInterface` | pass | 0:42:08.61 | 7,617,036 | 0:00:10.79 |
| `CameronProducts` | pass | 0:43:36.48 | 7,620,728 | 0:00:10.22 |
| `CameronSpatial` | pass | 0:46:22.61 | 7,621,832 | 0:00:09.68 |
| `CameronTemporalKernel` | pass | 0:46:06.64 | 7,618,036 | 0:00:08.45 |
| `CameronTemporalMap` | pass | 0:45:55.38 | 7,619,832 | 0:00:08.56 |
| `CameronTemporalSqrt` | pass | 0:54:21.77 | 7,569,096 | 0:00:08.36 |
| `CameronTemporalTarget` | pass | 0:43:34.40 | 7,622,300 | 0:00:08.41 |
| `CameronTemporalYoung` | pass | 0:42:58.17 | 7,617,112 | 0:00:08.15 |
| `CameronUMap` | pass | 0:41:40.69 | 7,638,636 | 0:00:08.65 |
| `CompactOperatorFoundation` | pass | 0:42:56.56 | 7,571,028 | 0:00:08.52 |
| `UniformMeanAssembly` | pass | 0:43:18.93 | 7,620,940 | 0:00:08.91 |
| `UniformMeanCutoff` | pass | 0:43:37.80 | 7,619,476 | 0:00:08.80 |
| `UniformMeanDischarge` | pass | 0:46:53.86 | 7,627,656 | 0:00:08.05 |
| `UniformMeanTensor` | pass | 0:43:39.22 | 7,617,232 | 0:00:08.39 |

## Coverage

`harness/closure-check.py` (unchanged since wave L5), run locally on
`8f51004` (the wave-L13/L14 replay commit, all 142 targets `--fresh`) against
`ebac849`, gives (`harness/closure-check.txt`): 19 new modules (the fifteen
above and the four of wave L15), 1 changed in content (the umbrella), 111
changed only in comments, 30 byte-identical, none removed, and one
import-closure gap, `Axioms`, which imports the umbrella. Of the 111
comment-only modules, 110 have unchanged line counts and one,
`GaussianScalarPowers`, has a changed line count (the wave-L15 README states
that all 111 have unchanged line counts; its own `closure-check.txt`, line 45,
already lists this one as changed). Against `315a332` (the wave-L15 replay
commit), the same script gives the fifteen new modules, the umbrella changed
in content, and the other 145 modules byte-identical.

So at `ebac849` the fifteen new modules and the umbrella are replayed
`--fresh`, and the umbrella's `--fresh` run re-checks every library module
except `Axioms` as an import. `Axioms` is replayed in default mode only (task 0). As
separate `--fresh` targets, the four wave-L15 modules were replayed at
`315a332` (byte-identical here) and the other 140 library modules at
`8f51004` (identical or comment-only here), plus default mode here.

**Not covered.** The comparator-tier Lake libraries `ChallengeDefs`,
`Challenge` and `Solution` are not imported by the umbrella and are not
built by `lake build StratonovichHAMSecondMoment`. This replay does not
check them.

## What was checked

| Item | Value |
|---|---|
| Commit | `ebac849d61e539a125de6d920c1c2b29255ca671` |
| Tree | `411f45b32cb77ef271136fd5dfa0fbe3c9254715` (checked by the build job before and after the build, and by every task before and after its replay) |
| Toolchain | `leanprover/lean4:v4.35.0`; Lean 4.35.0 (commit `eb6cafb7290e`), Lake 5.0.0 |
| Mathlib | `56a005855ea17e0b0958f73ec801ae140b0a1679`, checked by the build job and again by every task |
| `leanchecker` binary | sha256 `12c38901cdbfab178f1bf6145dd30012e9a3b2c11ca695292a5884fa3cbaddb6` (`lean` `bf8d54e4…`, `lake` `8ba83c98…`), the same binaries as in the wave-L5 to wave-L15 replays |
| Runtime | Lean 4.35.0 runtime tarball (sha256 `9bca7d29…`), extracted on the compute node, run inside the lab Apptainer image (Ubuntu 22.04) with `--cleanenv` |
| Workspace | the build job's sealed tarball `ws.tar.gz`, 2,591,939,701 bytes, sha256 `078d2cd1…09cff049`; every counted task checked this hash before unpacking |
| Host | Easley, partition `nova_20`, QOS `resourcecap_plus`. Build and pilot on node847; tasks 0 and 2 to 16 on node854 to node869, one per node |
| Build | `lake build StratonovichHAMSecondMoment StratonovichHAMSecondMoment.Axioms`: "Build completed successfully (9208 jobs)."; all 161 `.olean` files present |

`collect.py` binds every counted task to the build (commit, tree, inputs
hash, workspace tarball hash, `leanchecker` hash), checks that its target is
its manifest line and that its summary lists exactly that target with exit 0
and 0 output bytes (task 0: exactly the 161 manifest targets), and that
sacct shows the task `COMPLETED 0:0`.

## Commands

The private development repository was cloned on the login node over GitHub
ssh and `ebac849…` was checked out detached (`harness/stage-login.sh`). The
login node was reached through the <MACHINE> machine's connection (from the
laptop, `ssh <MACHINE> "ssh Easley bash -s"`); the frozen inputs were sent and
the evidence fetched the same way. `harness/preflight-login.sh` (with 2 CPUs
per task) passed before any submission (`MANIFEST_OK modules=161
fresh_targets=16`; the container has git, lake, lean, leanchecker, python3,
timeout, curl, tar, gzip and sha256sum on the job's PATH; output in
`harness/preflight/`).

Submission (`harness/submit.sh` with `CPUS=2 MEM=48G`, record in
`jobs.txt`):

```
sbatch build.sbatch                                                          # 5733053, --cpus-per-task=4 --mem=24G
sbatch --dependency=afterok:5733053 --array=1 --cpus-per-task=2 --mem=48G task.sbatch    # pilot 5733054
sbatch --array=0,2-16%100 --cpus-per-task=2 --mem=48G task.sbatch                        # rest 5733116
```

The rest was submitted once the pilot (the umbrella) printed
`REPLAY_STARTED`. Inside the container
(`PATH=<runtime>/bin:/usr/bin:/bin`, `LEAN_NUM_THREADS=3`,
`LAKE_ARTIFACT_CACHE=false`) each task ran

```
timeout -k 30s 3600s  lake env leanchecker <Module>           # task 0: default mode, all 161 targets, serial
timeout -k 30s 14400s lake env leanchecker --fresh <Module>   # task i >= 1: line i of targets-fresh.txt
```

**Open files.** No task waited for the `file-nr` guard (all `waited_s=0`,
`PRE_REPLAY file-nr` 1,280 to 1,560); the largest `file-nr` sample in the
monitors was 63,120.

## Accounting (sacct)

| Job | Role | Elapsed | TotalCPU | Alloc | MaxRSS (batch) |
|---|---|---|---|---|---|
| 5733053 | build | 0:20:37 | 0:54:32 | 4 CPU / 24G | 7,645,624 KB |
| 5733054 (`5733054_1`) | `--fresh` umbrella | 0:45:51 | 0:45:57 | 2 CPU / 48G | 8,115,412 KB |
| 5733118 (`5733116_2`) | `--fresh` `CameronFinal` | 0:46:01 | 0:45:55 | 2 CPU / 48G | 8,094,564 KB |
| 5733119 (`5733116_3`) | `--fresh` `CameronInterface` | 0:44:23 | 0:44:02 | 2 CPU / 48G | 7,094,772 KB |
| 5733120 (`5733116_4`) | `--fresh` `CameronProducts` | 0:46:01 | 0:45:32 | 2 CPU / 48G | 7,754,692 KB |
| 5733121 (`5733116_5`) | `--fresh` `CameronSpatial` | 0:49:00 | 0:48:21 | 2 CPU / 48G | 7,469,688 KB |
| 5733122 (`5733116_6`) | `--fresh` `CameronTemporalKernel` | 0:48:57 | 0:48:02 | 2 CPU / 48G | 7,404,196 KB |
| 5733123 (`5733116_7`) | `--fresh` `CameronTemporalMap` | 0:48:54 | 0:47:53 | 2 CPU / 48G | 7,744,932 KB |
| 5733124 (`5733116_8`) | `--fresh` `CameronTemporalSqrt` | 0:57:59 | 0:56:49 | 2 CPU / 48G | 7,208,268 KB |
| 5733125 (`5733116_9`) | `--fresh` `CameronTemporalTarget` | 0:46:58 | 0:45:31 | 2 CPU / 48G | 8,084,720 KB |
| 5733126 (`5733116_10`) | `--fresh` `CameronTemporalYoung` | 0:46:29 | 0:44:53 | 2 CPU / 48G | 7,212,612 KB |
| 5733127 (`5733116_11`) | `--fresh` `CameronUMap` | 0:45:22 | 0:43:34 | 2 CPU / 48G | 7,056,020 KB |
| 5733128 (`5733116_12`) | `--fresh` `CompactOperatorFoundation` | 0:47:02 | 0:44:04 | 2 CPU / 48G | 7,082,136 KB |
| 5733129 (`5733116_13`) | `--fresh` `UniformMeanAssembly` | 0:47:35 | 0:45:01 | 2 CPU / 48G | 6,867.50 MB |
| 5733130 (`5733116_14`) | `--fresh` `UniformMeanCutoff` | 0:47:56 | 0:45:35 | 2 CPU / 48G | 7,692,520 KB |
| 5733131 (`5733116_15`) | `--fresh` `UniformMeanDischarge` | 0:51:20 | 0:48:52 | 2 CPU / 48G | 7,118,536 KB |
| 5733116 (`5733116_16`) | `--fresh` `UniformMeanTensor` | 0:48:23 | 0:45:36 | 2 CPU / 48G | 8,079,148 KB |
| 5733117 (`5733116_0`) | default mode, 161 targets | 0:36:11 | 0:44:16 | 2 CPU / 48G | 24,644,068 KB |

Build phases: `lake exe cache get` 79 s (first attempt), build 812 s,
tarball 211 s. Task 0 replay phase 2,059 s for 161 targets (the umbrella
alone 0:11:20, peak RSS 25,208,640 KiB). Totals: 13:44:59 elapsed over the
18 jobs, TotalCPU 14:04:25.

**Wall time.** Build and pilot submitted 2026-11-20 11:58:52 CST; the rest
at 12:23:24; the last task ended at 13:21:24. From first submission to the
last task: **1:22:32**.

## Files

As in the wave-L15 folder: `summary.tsv` (one row per `--fresh` target:
module, exit, wall, peak RSS KiB, output bytes, job id), `fresh-time/`,
`default/summary-5733117.tsv`, `jobs/<job>/` (build logs and `BUILD_OK`;
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
