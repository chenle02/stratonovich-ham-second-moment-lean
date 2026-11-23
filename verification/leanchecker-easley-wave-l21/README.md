# External kernel replay on Easley, wave L21 (`leanchecker --fresh`, array gate, 2026-11-23)

Verification evidence at 38a3e00f9fc7: Easley leanchecker replay of wave L21 (2/2).

This is an independent replay of commit `38a3e00` on Auburn's Easley cluster
(Slurm). `38a3e00` is the wave-L21 gate commit on the integration branch
(`wave-l21/int`), the last commit changing Lean, claims or comparator files.
It is the thirteenth **array** gate, with the harness of the wave-L9 to
wave-L20 gates: every harness script (`stage-login.sh`, `preflight-login.sh`,
`build.sbatch`, `task.sbatch`, `submit.sh`, `collect.py`, `replay.py`) is
byte-identical to the wave-L20 folder's, as are `make-inputs.sh` (after
redaction) and `closure-check.py`. `pins.env`, `modules-all.txt`,
`targets-fresh.txt` and `INPUT-SHA256SUMS` name this commit; `pins.env`
differs from the wave-L20 one only in `EXPECTED_COMMIT` and `EXPECTED_TREE`.

The **one new library module** of wave L21 and the **umbrella** are replayed
`--fresh`, as at the wave-L20 gate:

```
StratonovichHAMSecondMoment
StratonovichHAMSecondMoment.SourceTubeAttained
```

`targets-fresh.txt` is this list, `LC_ALL=C` sorted (the file added under
`StratonovichHAMSecondMoment/` between `5cdd493` and `38a3e00`, plus the
umbrella). `modules-all.txt` is the manifest that `make-inputs.sh ... all`
writes (`git ls-tree` at `38a3e00`, sorted, then the umbrella). Array task
`i` (1 to 2) replays its line `i` with `lake env leanchecker --fresh`, which
also re-checks every transitive import (Lean core, Batteries, the imported
Mathlib slice and the project modules the target imports). The umbrella
imports every library module except `Axioms` (checked by the build job,
`MANIFEST_OK modules=212`), so its `--fresh` run re-checks those 210 library
modules as imports. Array task 0 replays all 212 manifest targets
(`modules-all.txt`: 211 library modules and the umbrella) in default mode, as
at every array gate.

**Result.** Both `--fresh` targets exit 0 with empty output, which is the
pass signature. All 212 targets pass default-mode replay
(`default/summary-5740996.tsv`). The build job and all 3 array tasks ended
`COMPLETED 0:0`, each with one attempt; no task was resubmitted.
`collect.py` exited 0 with verdict `COMPLETE` (`COLLECT.txt`).

| Module | `--fresh` | wall | peak RSS (KiB) | default-mode wall |
|---|---|---|---|---|
| umbrella `StratonovichHAMSecondMoment` | pass | 0:45:15.20 | 7,870,872 | 0:19:06.17 |
| `SourceTubeAttained` | pass | 0:42:45.32 | 7,573,000 | 0:00:08.73 |

## Coverage

`harness/closure-check.py` (unchanged since wave L5), run locally on the
laptop against `5cdd493` (the wave-L20 gate commit) and `38a3e00`, gives
(`harness/closure-check.txt`): 1 new module (`SourceTubeAttained`), 2 changed
in content (the umbrella, which imports `SourceTubeAttained`, and `Axioms`,
which gained the `#print axioms` lines of the twelve L21 declarations), 20
changed only in comments (the deferred docstring corrections of the wave-L20
reviews; 17 of them change the line count), 189 byte-identical, none removed,
and no import-closure gap (`Axioms` imports the umbrella and has no
importer). Against `8f51004` (the wave-L13/L14 replay commit, all 142 targets
`--fresh`) the same script gives 70 new modules (`SourceTubeAttained` and the
69 of waves L15 to L20), 2 changed in content (the umbrella and `Axioms`),
111 comment-only, 29 byte-identical, none removed.

So at `38a3e00` the new module and the umbrella are replayed `--fresh`, and
the umbrella's `--fresh` run re-checks every library module except `Axioms`
as an import, the 20 comment-only modules included. `Axioms` is replayed in
default mode only (task 0), as at every earlier array gate. As separate
`--fresh` targets, the eleven wave-L20 modules were replayed at `5cdd493`,
the eleven wave-L19 modules at `fe9f1de`, the thirteen wave-L18 modules at
`6e4644d`, the fifteen wave-L17 modules at `68d0c5e`, the fifteen wave-L16
modules at `ebac849`, the four wave-L15 modules at `315a332` and the other
140 library modules at `8f51004`; here each of them is byte-identical to
`5cdd493` or differs from it only in comments, and all pass default mode
here.

**Not covered.** The comparator-tier Lake libraries `ChallengeDefs`,
`Challenge` and `Solution` are not imported by the umbrella and are not
built by `lake build StratonovichHAMSecondMoment`. This replay does not
check them.

## What was checked

| Item | Value |
|---|---|
| Commit | `38a3e00f9fc70b847b442c658ba1dc2d47b462fc` |
| Tree | `4c9c0b2119e8f4bf79a7c3a1439b66416f8aef50` (checked by the build job before and after the build, and by every task before and after its replay) |
| Toolchain | `leanprover/lean4:v4.35.0`; Lean 4.35.0 (commit `eb6cafb7290e`), Lake 5.0.0 |
| Mathlib | `56a005855ea17e0b0958f73ec801ae140b0a1679`, checked by the build job and again by every task |
| `leanchecker` binary | sha256 `12c38901cdbfab178f1bf6145dd30012e9a3b2c11ca695292a5884fa3cbaddb6` (`lean` `bf8d54e4…`, `lake` `8ba83c98…`), the same binaries as in the wave-L5 to wave-L20 replays |
| Runtime | Lean 4.35.0 runtime tarball (sha256 `9bca7d29…`), extracted on the compute node, run inside the lab Apptainer image (Ubuntu 22.04) with `--cleanenv` |
| Workspace | the build job's sealed tarball `ws.tar.gz`, 2,632,660,363 bytes, sha256 `36426919…db903`; every counted task checked this hash before unpacking |
| Host | Easley, partition `nova_20`, QOS `resourcecap_plus`. Build and pilot on node845; task 0 on node862, task 2 on node863 |
| Build | `lake build StratonovichHAMSecondMoment StratonovichHAMSecondMoment.Axioms`: "Build completed successfully (9259 jobs)."; all 212 `.olean` files present |

`collect.py` binds every counted task to the build (commit, tree, inputs
hash, workspace tarball hash, `leanchecker` hash), checks that its target is
its manifest line and that its summary lists exactly that target with exit 0
and 0 output bytes (task 0: exactly the 212 manifest targets), and that
sacct shows the task `COMPLETED 0:0`.

## Commands

The local precondition (CLAUDE.md HPC rule 1) is the <MACHINE> build of the
umbrella and `Axioms` for wave L21 (9259 jobs, 0 warnings, recorded in the
wave-L21 row of `COMPLETION.md`) and the <MACHINE> comparator build at
`aa23c99`; the library modules, `lakefile.toml`, `lake-manifest.json` and
`lean-toolchain` are byte-identical between `aa23c99` and `38a3e00`, which
touches claims and comparator files only. The Easley build of `38a3e00` gives
the same 9259 jobs.

The private development repository was cloned on the login node over GitHub
ssh and `38a3e00…` was checked out detached (`harness/stage-login.sh`). The
login node was reached through the <MACHINE> machine's connection (from the
laptop, `ssh <MACHINE> "ssh Easley bash -s"`); the frozen inputs were sent and
the evidence fetched the same way. `harness/preflight-login.sh` (with 2 CPUs
per task) passed before any submission (`MANIFEST_OK modules=212
fresh_targets=2`; the container has git, lake, lean, leanchecker, python3,
timeout, curl, tar, gzip and sha256sum on the job's PATH; QOS headroom
208 of 1440 CPUs in use, 10 needed; output in `harness/preflight/`).

Submission (`harness/submit.sh` with `CPUS=2 MEM=48G`, record in
`jobs.txt`):

```
sbatch build.sbatch                                                          # 5740993, --cpus-per-task=4 --mem=24G
sbatch --dependency=afterok:5740993 --array=1 --cpus-per-task=2 --mem=48G task.sbatch    # pilot 5740994
sbatch --array=0,2-2%100 --cpus-per-task=2 --mem=48G task.sbatch                         # rest 5740995
```

The allocation was not raised from the wave-L20 gate: there the umbrella's
default-mode peak RSS was 21,629,344 KiB (sacct MaxRSS 21.6 GB), under the
48G allocation. The rest was submitted once the pilot (the umbrella) printed
`REPLAY_STARTED`. Inside the container
(`PATH=<runtime>/bin:/usr/bin:/bin`, `LEAN_NUM_THREADS=3`,
`LAKE_ARTIFACT_CACHE=false`) each task ran

```
timeout -k 30s 3600s  lake env leanchecker <Module>           # task 0: default mode, all 212 targets, serial
timeout -k 30s 14400s lake env leanchecker --fresh <Module>   # task i >= 1: line i of targets-fresh.txt
```

**Mathlib cache.** The build job's first `lake exe cache get` completed in
72 s (`CACHE attempt=1 rc=0`, `jobs/5740993/cache-get-1.log`); no retry was
needed. The build then started from no project `.olean`
(`NO_PROJECT_OLEANS_BEFORE_BUILD`).

**Open files.** No task waited for the `file-nr` guard (all `waited_s=0`,
`PRE_REPLAY file-nr` 1,240 to 1,440); the largest `file-nr` sample in the
monitors was 63,360.

## Accounting (sacct)

| Job | Role | Elapsed | TotalCPU | Alloc | MaxRSS (batch) |
|---|---|---|---|---|---|
| 5740993 | build | 0:23:18 | 1:05:04 | 4 CPU / 24G | 7,122,636 KB |
| 5740994 (`5740994_1`) | `--fresh` umbrella | 0:47:07 | 0:47:12 | 2 CPU / 48G | 8,065,020 KB |
| 5740995 (`5740995_2`) | `--fresh` `SourceTubeAttained` | 0:44:50 | 0:44:43 | 2 CPU / 48G | 7,812,028 KB |
| 5740996 (`5740995_0`) | default mode, 212 targets | 0:52:52 | 1:07:24 | 2 CPU / 48G | 21,788,544 KB |

Build phases: `lake exe cache get` 72 s (one attempt), build 1,006 s,
tarball 214 s. Task 0 replay phase 3,070 s for 212 targets (the umbrella
alone 0:19:06, peak RSS 21,995,796 KiB, against 21,629,344 KiB at the
wave-L20 gate, within the 48G allocation). The job's memory cgroup
(`jobs/5740996/monitor.log`, `mem_max`, which also counts page cache)
peaked at 37,283,811,328 bytes; the process peak RSS above is the relevant
figure. Totals: 2:48:07 elapsed over the 4 jobs, TotalCPU 3:44:23.

**Wall time.** Build and pilot submitted 2026-11-23 04:41:31 CST; the rest
at 05:08:04; the last task ended at 06:00:57. From first submission to the
last task: **1:19:26**.

## Files

As in the wave-L20 folder: `summary.tsv` (one row per `--fresh` target:
module, exit, wall, peak RSS KiB, output bytes, job id), `fresh-time/`,
`default/summary-5740996.tsv`, `jobs/<job>/` (build logs and `BUILD_OK`;
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
