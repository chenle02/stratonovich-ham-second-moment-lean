# External kernel replay on Easley, wave L20 (`leanchecker --fresh`, array gate, 2026-11-23)

Verification evidence at 5cdd49359fa0: Easley leanchecker replay of wave L20 (12/12).

This is an independent replay of commit `5cdd493` on Auburn's Easley cluster
(Slurm). `5cdd493` is the wave-L20 gate commit on the integration branch
(`wave-l20/int`), the last commit changing Lean, claims or comparator files.
It is the twelfth **array** gate, with the harness of the wave-L9 to wave-L19
gates: every harness script (`stage-login.sh`, `preflight-login.sh`,
`build.sbatch`, `task.sbatch`, `submit.sh`, `collect.py`, `replay.py`) is
byte-identical to the wave-L19 folder's, as are `make-inputs.sh` (after
redaction) and `closure-check.py`. `pins.env`, `modules-all.txt`,
`targets-fresh.txt` and `INPUT-SHA256SUMS` name this commit.

The **eleven new library modules** of wave L20 and the **umbrella** are
replayed `--fresh`, as at the wave-L19 gate:

```
StratonovichHAMSecondMoment
StratonovichHAMSecondMoment.CleanupWrappers
StratonovichHAMSecondMoment.MildConstruction
StratonovichHAMSecondMoment.MildFields
StratonovichHAMSecondMoment.MildFinal
StratonovichHAMSecondMoment.MildGreenWidth
StratonovichHAMSecondMoment.MildInterface
StratonovichHAMSecondMoment.MildOccupied
StratonovichHAMSecondMoment.MildPartialVertex
StratonovichHAMSecondMoment.MildPolyMem
StratonovichHAMSecondMoment.MildTerminalFubini
StratonovichHAMSecondMoment.RieszInstanceOne
```

`targets-fresh.txt` is this list, `LC_ALL=C` sorted (made by
`make-inputs.sh ... all` and then replaced by these twelve lines: the files
added under `StratonovichHAMSecondMoment/` between `fe9f1de` and `5cdd493`,
plus the umbrella, with `INPUT-SHA256SUMS` recomputed). Array task `i` (1 to
12) replays its line `i` with `lake env leanchecker --fresh`, which also
re-checks every transitive import (Lean core, Batteries, the imported Mathlib
slice and the project modules the target imports). The umbrella imports every
library module except `Axioms` (checked by the build job, `MANIFEST_OK
modules=211`), so its `--fresh` run re-checks those 209 library modules as
imports. Array task 0 replays all 211 manifest targets (`modules-all.txt`:
210 library modules and the umbrella) in default mode, as at every array
gate.

**Result.** All 12 `--fresh` targets exit 0 with empty output, which is the
pass signature. All 211 targets pass default-mode replay
(`default/summary-5740982.tsv`). The build job and all 13 array tasks ended
`COMPLETED 0:0`, each with one attempt; no task was resubmitted.
`collect.py` exited 0 with verdict `COMPLETE` (`COLLECT.txt`).

| Module | `--fresh` | wall | peak RSS (KiB) | default-mode wall |
|---|---|---|---|---|
| umbrella `StratonovichHAMSecondMoment` | pass | 0:44:06.87 | 7,875,056 | 0:19:11.36 |
| `CleanupWrappers` | pass | 0:43:25.49 | 7,677,016 | 0:00:08.90 |
| `MildConstruction` | pass | 0:41:55.39 | 7,690,128 | 0:00:08.98 |
| `MildFields` | pass | 0:41:58.57 | 7,690,948 | 0:00:09.05 |
| `MildFinal` | pass | 0:53:45.51 | 7,697,400 | 0:00:08.73 |
| `MildGreenWidth` | pass | 0:41:53.26 | 7,688,832 | 0:00:09.70 |
| `MildInterface` | pass | 0:41:59.65 | 7,689,076 | 0:00:08.99 |
| `MildOccupied` | pass | 0:41:48.74 | 7,695,964 | 0:00:09.15 |
| `MildPartialVertex` | pass | 0:42:15.12 | 7,671,952 | 0:00:08.98 |
| `MildPolyMem` | pass | 0:43:22.24 | 7,669,620 | 0:00:08.86 |
| `MildTerminalFubini` | pass | 0:43:35.79 | 7,670,512 | 0:00:09.09 |
| `RieszInstanceOne` | pass | 0:43:11.82 | 7,618,880 | 0:00:09.47 |

## Coverage

`harness/closure-check.py` (unchanged since wave L5), run locally on the
laptop against `fe9f1de` (the wave-L19 gate commit) and `5cdd493`, gives
(`harness/closure-check.txt`): 11 new modules (the eleven above), 2 changed
in content (the umbrella, which imports `MildFinal`, and `Axioms`, which
gained the `#print axioms` lines of the L20 modules), 39 changed only in
comments (the DOC docstring pass), 159 byte-identical, none removed, and no
import-closure gap (`Axioms` imports the umbrella and has no importer).
Against `8f51004` (the wave-L13/L14 replay commit, all 142 targets
`--fresh`) the same script gives 69 new modules (the eleven above and the
58 of waves L15 to L19), 2 changed in content (the umbrella and `Axioms`),
111 comment-only, 29 byte-identical, none removed.

So at `5cdd493` the eleven new modules and the umbrella are replayed
`--fresh`, and the umbrella's `--fresh` run re-checks every library module
except `Axioms` as an import, the 39 comment-only modules included.
`Axioms` is replayed in default mode only (task 0), as at every earlier
array gate. As separate `--fresh` targets, the eleven wave-L19 modules were
replayed at `fe9f1de`, the thirteen wave-L18 modules at `6e4644d`, the
fifteen wave-L17 modules at `68d0c5e`, the fifteen wave-L16 modules at
`ebac849`, the four wave-L15 modules at `315a332` and the other 140 library
modules at `8f51004`; here each of them is byte-identical to `fe9f1de` or
differs from it only in comments, and all pass default mode here.

**Not covered.** The comparator-tier Lake libraries `ChallengeDefs`,
`Challenge` and `Solution` are not imported by the umbrella and are not
built by `lake build StratonovichHAMSecondMoment`. This replay does not
check them.

## What was checked

| Item | Value |
|---|---|
| Commit | `5cdd49359fa093549572a890e68a7d25f412733e` |
| Tree | `cfcb9596b53f9a56fb5da24922f3bb98f9094608` (checked by the build job before and after the build, and by every task before and after its replay) |
| Toolchain | `leanprover/lean4:v4.35.0`; Lean 4.35.0 (commit `eb6cafb7290e`), Lake 5.0.0 |
| Mathlib | `56a005855ea17e0b0958f73ec801ae140b0a1679`, checked by the build job and again by every task |
| `leanchecker` binary | sha256 `12c38901cdbfab178f1bf6145dd30012e9a3b2c11ca695292a5884fa3cbaddb6` (`lean` `bf8d54e4…`, `lake` `8ba83c98…`), the same binaries as in the wave-L5 to wave-L19 replays |
| Runtime | Lean 4.35.0 runtime tarball (sha256 `9bca7d29…`), extracted on the compute node, run inside the lab Apptainer image (Ubuntu 22.04) with `--cleanenv` |
| Workspace | the build job's sealed tarball `ws.tar.gz`, 2,631,931,588 bytes, sha256 `222e0098…f2ac0`; every counted task checked this hash before unpacking |
| Host | Easley, partition `nova_20`, QOS `resourcecap_plus`. Build and pilot on node845; tasks 0 and 2 to 12 on twelve other nodes (node862 to node927), one per node |
| Build | `lake build StratonovichHAMSecondMoment StratonovichHAMSecondMoment.Axioms`: "Build completed successfully (9258 jobs)."; all 211 `.olean` files present |

`collect.py` binds every counted task to the build (commit, tree, inputs
hash, workspace tarball hash, `leanchecker` hash), checks that its target is
its manifest line and that its summary lists exactly that target with exit 0
and 0 output bytes (task 0: exactly the 211 manifest targets), and that
sacct shows the task `COMPLETED 0:0`.

## Commands

The local precondition (CLAUDE.md HPC rule 1) is the <MACHINE> build of the
umbrella and `Axioms` at `1b3cb25` (9258 jobs, recorded in the wave-L20 row
of `COMPLETION.md`); the commits from there to `5cdd493` change the library
modules only in comments (`3d651aa`) or touch claims and comparator files
only. The Easley build of `5cdd493` gives the same 9258 jobs.

The private development repository was cloned on the login node over GitHub
ssh and `5cdd493…` was checked out detached (`harness/stage-login.sh`). The
login node was reached through the <MACHINE> machine's connection (from the
laptop, `ssh <MACHINE> "ssh Easley bash -s"`); the frozen inputs were sent and
the evidence fetched the same way. `harness/preflight-login.sh` (with 2 CPUs
per task) passed before any submission (`MANIFEST_OK modules=211
fresh_targets=12`; the container has git, lake, lean, leanchecker, python3,
timeout, curl, tar, gzip and sha256sum on the job's PATH; QOS headroom
208 of 1440 CPUs in use, 30 needed; output in `harness/preflight/`).

Submission (`harness/submit.sh` with `CPUS=2 MEM=48G`, record in
`jobs.txt`):

```
sbatch build.sbatch                                                          # 5740976, --cpus-per-task=4 --mem=24G
sbatch --dependency=afterok:5740976 --array=1 --cpus-per-task=2 --mem=48G task.sbatch    # pilot 5740977
sbatch --array=0,2-12%100 --cpus-per-task=2 --mem=48G task.sbatch                        # rest 5740981
```

The allocation was not raised from the wave-L19 gate: there the umbrella's
default-mode peak RSS was 23,721,152 KiB, about half of the 48G allocation.
The rest was submitted once the pilot (the umbrella) printed
`REPLAY_STARTED`. Inside the container
(`PATH=<runtime>/bin:/usr/bin:/bin`, `LEAN_NUM_THREADS=3`,
`LAKE_ARTIFACT_CACHE=false`) each task ran

```
timeout -k 30s 3600s  lake env leanchecker <Module>           # task 0: default mode, all 211 targets, serial
timeout -k 30s 14400s lake env leanchecker --fresh <Module>   # task i >= 1: line i of targets-fresh.txt
```

**Mathlib cache.** The build job's first `lake exe cache get` completed in
90 s (`CACHE attempt=1 rc=0`, `jobs/5740976/cache-get-1.log`); no retry was
needed. The build then started from no project `.olean`
(`NO_PROJECT_OLEANS_BEFORE_BUILD`).

**Open files.** No task waited for the `file-nr` guard (all `waited_s=0`,
`PRE_REPLAY file-nr` 1,320 to 1,520); the largest `file-nr` sample in the
monitors was 63,400.

## Accounting (sacct)

| Job | Role | Elapsed | TotalCPU | Alloc | MaxRSS (batch) |
|---|---|---|---|---|---|
| 5740976 | build | 0:23:41 | 1:04:58 | 4 CPU / 24G | 7,344,904 KB |
| 5740977 (`5740977_1`) | `--fresh` umbrella | 0:46:03 | 0:46:03 | 2 CPU / 48G | 7,301,012 KB |
| 5740983 (`5740981_2`) | `--fresh` `CleanupWrappers` | 0:45:30 | 0:45:23 | 2 CPU / 48G | 7,682,212 KB |
| 5740984 (`5740981_3`) | `--fresh` `MildConstruction` | 0:44:13 | 0:43:52 | 2 CPU / 48G | 7,368,176 KB |
| 5740985 (`5740981_4`) | `--fresh` `MildFields` | 0:44:23 | 0:43:55 | 2 CPU / 48G | 7,091,032 KB |
| 5740986 (`5740981_5`) | `--fresh` `MildFinal` | 0:56:47 | 0:56:11 | 2 CPU / 48G | 8,038,728 KB |
| 5740987 (`5740981_6`) | `--fresh` `MildGreenWidth` | 0:44:45 | 0:43:49 | 2 CPU / 48G | 7,227,788 KB |
| 5740988 (`5740981_7`) | `--fresh` `MildInterface` | 0:44:58 | 0:43:56 | 2 CPU / 48G | 7,151,860 KB |
| 5740989 (`5740981_8`) | `--fresh` `MildOccupied` | 0:44:58 | 0:43:45 | 2 CPU / 48G | 8,088,596 KB |
| 5740990 (`5740981_9`) | `--fresh` `MildPartialVertex` | 0:45:35 | 0:44:12 | 2 CPU / 48G | 8,014,724 KB |
| 5740991 (`5740981_10`) | `--fresh` `MildPolyMem` | 0:46:55 | 0:45:19 | 2 CPU / 48G | 7,995,088 KB |
| 5740992 (`5740981_11`) | `--fresh` `MildTerminalFubini` | 0:47:21 | 0:45:34 | 2 CPU / 48G | 8,095,188 KB |
| 5740981 (`5740981_12`) | `--fresh` `RieszInstanceOne` | 0:47:06 | 0:45:09 | 2 CPU / 48G | 6,998,328 KB |
| 5740982 (`5740981_0`) | default mode, 211 targets | 0:53:00 | 1:07:39 | 2 CPU / 48G | 21,606,512 KB |

Build phases: `lake exe cache get` 90 s (one attempt), build 1,000 s,
tarball 217 s. Task 0 replay phase 3,078 s for 211 targets (the umbrella
alone 0:19:11, peak RSS 21,629,344 KiB, against 23,721,152 KiB at the
wave-L19 gate, within the 48G allocation). The job's memory cgroup
(`jobs/5740982/monitor.log`, `mem_max`, which also counts page cache)
peaked at 36,969,271,296 bytes; the process peak RSS above is the relevant
figure. Totals: 10:35:15 elapsed over the 14 jobs, TotalCPU 11:19:45.

**Wall time.** Build and pilot submitted 2026-11-23 02:32:51 CST; the rest
at 02:59:19; the last task ended at 03:56:07. From first submission to the
last task: **1:23:16**.

## Files

As in the wave-L19 folder: `summary.tsv` (one row per `--fresh` target:
module, exit, wall, peak RSS KiB, output bytes, job id), `fresh-time/`,
`default/summary-5740982.tsv`, `jobs/<job>/` (build logs and `BUILD_OK`;
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
