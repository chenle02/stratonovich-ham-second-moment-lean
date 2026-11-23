# External kernel replay on Easley, wave L19 (`leanchecker --fresh`, array gate, 2026-11-22)

Verification evidence at fe9f1de63d87: Easley leanchecker replay of wave L19 (12/12).

This is an independent replay of commit `fe9f1de` on Auburn's Easley cluster
(Slurm). `fe9f1de` is the wave-L19 gate commit on the integration branch
(`wave-l19/int`). It is the eleventh **array** gate, with the harness of the
wave-L9 to wave-L18 gates: every harness script (`stage-login.sh`,
`preflight-login.sh`, `build.sbatch`, `task.sbatch`, `submit.sh`,
`collect.py`, `replay.py`) is byte-identical to the wave-L18 folder's, as
are `make-inputs.sh` (after redaction) and `closure-check.py`. `pins.env`,
`modules-all.txt`, `targets-fresh.txt` and `INPUT-SHA256SUMS` name this
commit.

The **eleven new library modules** of wave L19 and the **umbrella** are
replayed `--fresh`, as at the wave-L18 gate:

```
StratonovichHAMSecondMoment
StratonovichHAMSecondMoment.SourceExpansion
StratonovichHAMSecondMoment.SourceFeatures
StratonovichHAMSecondMoment.SourceFinal
StratonovichHAMSecondMoment.SourceFixedOrder
StratonovichHAMSecondMoment.SourceGreenFirst
StratonovichHAMSecondMoment.SourceInterface
StratonovichHAMSecondMoment.SourceIsonormal
StratonovichHAMSecondMoment.SourceMixed
StratonovichHAMSecondMoment.SourceReversal
StratonovichHAMSecondMoment.SourceVertexCrude
StratonovichHAMSecondMoment.SourceWick
```

`targets-fresh.txt` is this list, `LC_ALL=C` sorted (made by
`make-inputs.sh ... all` and then replaced by these twelve lines: the files
added under `StratonovichHAMSecondMoment/` between `6e4644d` and `fe9f1de`,
plus the umbrella, with `INPUT-SHA256SUMS` recomputed). Array task `i` (1 to
12) replays its line `i` with `lake env leanchecker --fresh`, which also
re-checks every transitive import (Lean core, Batteries, the imported Mathlib
slice and the project modules the target imports). The umbrella imports every
library module except `Axioms` (checked by the build job, `MANIFEST_OK
modules=200`), so its `--fresh` run re-checks those 198 library modules as
imports. Array task 0 replays all 200 manifest targets (`modules-all.txt`:
199 library modules and the umbrella) in default mode, as at every array
gate.

**Result.** All 12 `--fresh` targets exit 0 with empty output, which is the
pass signature. All 200 targets pass default-mode replay
(`default/summary-5740636.tsv`). The build job and all 13 array tasks ended
`COMPLETED 0:0`, each with one attempt; no task was resubmitted.
`collect.py` exited 0 with verdict `COMPLETE` (`COLLECT.txt`).

| Module | `--fresh` | wall | peak RSS (KiB) | default-mode wall |
|---|---|---|---|---|
| umbrella `StratonovichHAMSecondMoment` | pass | 0:45:32.06 | 7,860,544 | 0:15:04.10 |
| `SourceExpansion` | pass | 0:43:38.61 | 7,658,696 | 0:00:08.28 |
| `SourceFeatures` | pass | 0:42:12.90 | 7,660,552 | 0:00:08.45 |
| `SourceFinal` | pass | 0:42:19.48 | 7,676,052 | 0:00:08.40 |
| `SourceFixedOrder` | pass | 0:42:30.01 | 7,657,948 | 0:00:08.37 |
| `SourceGreenFirst` | pass | 0:42:07.74 | 7,656,844 | 0:00:08.32 |
| `SourceInterface` | pass | 0:42:16.29 | 7,656,600 | 0:00:08.41 |
| `SourceIsonormal` | pass | 0:43:35.46 | 7,657,080 | 0:00:08.68 |
| `SourceMixed` | pass | 0:45:50.43 | 7,658,048 | 0:00:08.37 |
| `SourceReversal` | pass | 0:43:35.16 | 7,658,948 | 0:00:08.79 |
| `SourceVertexCrude` | pass | 0:44:20.32 | 7,655,820 | 0:00:08.47 |
| `SourceWick` | pass | 0:43:37.82 | 7,657,132 | 0:00:08.41 |

## Coverage

`harness/closure-check.py` (unchanged since wave L5), run locally on
`6e4644d` (the wave-L18 replay commit) against `fe9f1de`, gives
(`harness/closure-check.txt`): 11 new modules (the eleven above), 1 changed
in content (the umbrella), 0 changed only in comments, 188 byte-identical,
none removed, and one import-closure gap, `Axioms`, which imports the
umbrella. Against `8f51004` (the wave-L13/L14 replay commit, all 142 targets
`--fresh`) the same script gives 58 new modules (the eleven above, the
thirteen of wave L18, the fifteen of wave L17, the fifteen of wave L16 and
the four of wave L15), the umbrella changed in content, 111 comment-only, 30
byte-identical, none removed.

So at `fe9f1de` the eleven new modules and the umbrella are replayed
`--fresh`, and the umbrella's `--fresh` run re-checks every library module
except `Axioms` as an import. `Axioms` is replayed in default mode only
(task 0). As separate `--fresh` targets, the thirteen wave-L18 modules were
replayed at `6e4644d`, the fifteen wave-L17 modules at `68d0c5e`, the
fifteen wave-L16 modules at `ebac849`, the four wave-L15 modules at
`315a332` and the other 140 library modules at `8f51004`; all of them are
byte-identical here to `6e4644d`, and they also pass default mode here.

**Not covered.** The comparator-tier Lake libraries `ChallengeDefs`,
`Challenge` and `Solution` are not imported by the umbrella and are not
built by `lake build StratonovichHAMSecondMoment`. This replay does not
check them.

## What was checked

| Item | Value |
|---|---|
| Commit | `fe9f1de63d87a96443eafb5979a63c334808241c` |
| Tree | `e7faafb1d463a4a1cda54a7627cba536e08df95e` (checked by the build job before and after the build, and by every task before and after its replay) |
| Toolchain | `leanprover/lean4:v4.35.0`; Lean 4.35.0 (commit `eb6cafb7290e`), Lake 5.0.0 |
| Mathlib | `56a005855ea17e0b0958f73ec801ae140b0a1679`, checked by the build job and again by every task |
| `leanchecker` binary | sha256 `12c38901cdbfab178f1bf6145dd30012e9a3b2c11ca695292a5884fa3cbaddb6` (`lean` `bf8d54e4…`, `lake` `8ba83c98…`), the same binaries as in the wave-L5 to wave-L18 replays |
| Runtime | Lean 4.35.0 runtime tarball (sha256 `9bca7d29…`), extracted on the compute node, run inside the lab Apptainer image (Ubuntu 22.04) with `--cleanenv` |
| Workspace | the build job's sealed tarball `ws.tar.gz`, 2,623,209,679 bytes, sha256 `f56cf664…ba0c`; every counted task checked this hash before unpacking |
| Host | Easley, partition `nova_20`, QOS `resourcecap_plus`. Build and pilot on node835; tasks 0 and 2 to 12 on twelve other nodes (node846 to node948), one per node |
| Build | `lake build StratonovichHAMSecondMoment StratonovichHAMSecondMoment.Axioms`: "Build completed successfully (9247 jobs)."; all 200 `.olean` files present |

`collect.py` binds every counted task to the build (commit, tree, inputs
hash, workspace tarball hash, `leanchecker` hash), checks that its target is
its manifest line and that its summary lists exactly that target with exit 0
and 0 output bytes (task 0: exactly the 200 manifest targets), and that
sacct shows the task `COMPLETED 0:0`.

## Commands

The local precondition (CLAUDE.md HPC rule 1) is the <MACHINE> build of the
umbrella and `Axioms` at `8e61d09` (9247 jobs, recorded in the wave-L19 row
of `COMPLETION.md`); the commits from there to `fe9f1de` change the library
modules only in comments.

The private development repository was cloned on the login node over GitHub
ssh and `fe9f1de…` was checked out detached (`harness/stage-login.sh`). The
login node was reached through the <MACHINE> machine's connection (from the
laptop, `ssh <MACHINE> "ssh Easley bash -s"`); the frozen inputs were sent and
the evidence fetched the same way. `harness/preflight-login.sh` (with 2 CPUs
per task) passed before any submission (`MANIFEST_OK modules=200
fresh_targets=12`; the container has git, lake, lean, leanchecker, python3,
timeout, curl, tar, gzip and sha256sum on the job's PATH; QOS headroom
213 of 1440 CPUs in use, 30 needed; output in `harness/preflight/`).

Submission (`harness/submit.sh` with `CPUS=2 MEM=48G`, record in
`jobs.txt`):

```
sbatch build.sbatch                                                          # 5740610, --cpus-per-task=4 --mem=24G
sbatch --dependency=afterok:5740610 --array=1 --cpus-per-task=2 --mem=48G task.sbatch    # pilot 5740611
sbatch --array=0,2-12%100 --cpus-per-task=2 --mem=48G task.sbatch                        # rest 5740635
```

The rest was submitted once the pilot (the umbrella) printed
`REPLAY_STARTED`. Inside the container
(`PATH=<runtime>/bin:/usr/bin:/bin`, `LEAN_NUM_THREADS=3`,
`LAKE_ARTIFACT_CACHE=false`) each task ran

```
timeout -k 30s 3600s  lake env leanchecker <Module>           # task 0: default mode, all 200 targets, serial
timeout -k 30s 14400s lake env leanchecker --fresh <Module>   # task i >= 1: line i of targets-fresh.txt
```

**Mathlib cache.** The build job's first `lake exe cache get` completed in
75 s (`CACHE attempt=1 rc=0`, `jobs/5740610/cache-get-1.log`); no retry was
needed. The build then started from no project `.olean`
(`NO_PROJECT_OLEANS_BEFORE_BUILD`).

**Open files.** No task waited for the `file-nr` guard (all `waited_s=0`,
`PRE_REPLAY file-nr` 1,200 to 1,560); the largest `file-nr` sample in the
monitors was 63,280.

## Accounting (sacct)

| Job | Role | Elapsed | TotalCPU | Alloc | MaxRSS (batch) |
|---|---|---|---|---|---|
| 5740610 | build | 0:23:10 | 1:07:10 | 4 CPU / 24G | 7,218,196 KB |
| 5740611 (`5740611_1`) | `--fresh` umbrella | 0:47:39 | 0:47:27 | 2 CPU / 48G | 8,251,628 KB |
| 5740637 (`5740635_2`) | `--fresh` `SourceExpansion` | 0:45:43 | 0:45:37 | 2 CPU / 48G | 7,111,344 KB |
| 5740638 (`5740635_3`) | `--fresh` `SourceFeatures` | 0:44:27 | 0:44:09 | 2 CPU / 48G | 7,177,568 KB |
| 5740639 (`5740635_4`) | `--fresh` `SourceFinal` | 0:44:45 | 0:44:17 | 2 CPU / 48G | 7,542,980 KB |
| 5740640 (`5740635_5`) | `--fresh` `SourceFixedOrder` | 0:45:08 | 0:44:25 | 2 CPU / 48G | 8,103,400 KB |
| 5740641 (`5740635_6`) | `--fresh` `SourceGreenFirst` | 0:44:55 | 0:44:03 | 2 CPU / 48G | 7,128,628 KB |
| 5740642 (`5740635_7`) | `--fresh` `SourceInterface` | 0:45:15 | 0:44:13 | 2 CPU / 48G | 7,608,936 KB |
| 5740643 (`5740635_8`) | `--fresh` `SourceIsonormal` | 0:46:47 | 0:45:33 | 2 CPU / 48G | 7,066,328 KB |
| 5740644 (`5740635_9`) | `--fresh` `SourceMixed` | 0:49:12 | 0:47:49 | 2 CPU / 48G | 8,006,572 KB |
| 5740645 (`5740635_10`) | `--fresh` `SourceReversal` | 0:48:30 | 0:45:31 | 2 CPU / 48G | 7,829,532 KB |
| 5740646 (`5740635_11`) | `--fresh` `SourceVertexCrude` | 0:48:22 | 0:45:37 | 2 CPU / 48G | 7,293,212 KB |
| 5740635 (`5740635_12`) | `--fresh` `SourceWick` | 0:47:31 | 0:45:35 | 2 CPU / 48G | 7,834,732 KB |
| 5740636 (`5740635_0`) | default mode, 200 targets | 0:45:43 | 0:56:42 | 2 CPU / 48G | 22,993,788 KB |

Build phases: `lake exe cache get` 75 s (one attempt), build 1,018 s,
tarball 214 s. Task 0 replay phase 2,642 s for 200 targets (the umbrella
alone 0:15:04, peak RSS 23,721,152 KiB, against 24,547,540 KiB at the
wave-L18 gate, within the 48G allocation). The job's memory cgroup
(`jobs/5740636/monitor.log`, `mem_max`, which also counts page cache)
peaked at 39,397,359,616 bytes; the process peak RSS above is the relevant
figure, and the allocation was not raised. Totals: 10:27:07 elapsed over the
14 jobs, TotalCPU 11:08:08.

**Wall time.** Build and pilot submitted 2026-11-22 18:04:27 CST; the rest
at 18:30:03; the last task ended at 19:19:16. From first submission to the
last task: **1:14:49**.

## Files

As in the wave-L18 folder: `summary.tsv` (one row per `--fresh` target:
module, exit, wall, peak RSS KiB, output bytes, job id), `fresh-time/`,
`default/summary-5740636.tsv`, `jobs/<job>/` (build logs and `BUILD_OK`;
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
