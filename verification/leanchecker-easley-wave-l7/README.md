# External kernel replay on Easley, wave L7 (`leanchecker --fresh`, 2026-11-12)

This is an independent replay of commit `f3be834` on Auburn's Easley cluster
(Slurm). `f3be834` is the commit at which the wave-L7 correspondence gate
closed (the author closed it on 2026-11-12, as recorded in the README at
`ed3cd68`). The job started from a fresh clone and a fresh build. Each target
is replayed by its own `lake env leanchecker --fresh <Module>` run, which also
re-checks every transitive import (Lean core, Batteries and the imported
Mathlib slice).

**Result.** All 10 targets exit 0 with empty output, which is the pass
signature. The job completed with one attempt and no failures.

All 81 targets (80 modules plus the umbrella) also passed default-mode
replay in this job (`default/summary-5692712.tsv`).

## Covered modules

The eight modules new in wave L7:

- `StratonovichHAMSecondMoment.InventoryProduct`
- `StratonovichHAMSecondMoment.UniformSeriesTail`
- `StratonovichHAMSecondMoment.H1Density`
- `StratonovichHAMSecondMoment.SpatialFourLinear`
- `StratonovichHAMSecondMoment.OccupationPhysicalClass`
- `StratonovichHAMSecondMoment.IntervalScalar`
- `StratonovichHAMSecondMoment.IntervalScalarCompleted`
- `StratonovichHAMSecondMoment.SpatialOccupationL7Completed`

Two targets whose source changed in content after the wave-L6 replay commit
`bfa2fd0`:

- the umbrella `StratonovichHAMSecondMoment` (imports of the eight new
  modules);
- `StratonovichHAMSecondMoment.Axioms` (`#print axioms` lines for them).

### Import-closure check

`harness/closure-check.py` is the wave-L5 script, copied unchanged (same
sha256 as in `verification/leanchecker-easley-wave-l5/harness/` and
`verification/leanchecker-easley-wave-l6/harness/`). It reads both commits
with `git show` only. For each library module it strips the Lean comments
(`/- -/`, nested, which covers doc comments and module docs, and `--` line
comments; string and character literals are kept) and compares the result at
`f3be834` with the source at an earlier commit. It then computes each
module's transitive project imports at `f3be834` and lists every unchanged
module that imports a new or changed one. Its output is in
`harness/closure-check.txt`.

Relative to `bfa2fd0` it finds 8 new modules, 2 changed in content (the
umbrella and `Axioms`), 35 changed only in comments and 36 byte-identical.
No module was removed, and no unchanged module imports a new or changed one:
the eight new modules are imported only by the umbrella, and the umbrella
only by `Axioms`.

The 35 comment-only modules are all `StratonovichHAMSecondMoment` modules
(no `StratonovichHAMAudit` file changed between `bfa2fd0` and `f3be834`).
Their doc comments changed in the wave-L7 review repairs and in the re-anchor
of TeX line citations to manuscript revision `a284420` (commits `319cc2e`,
`979c5fe` and `f3be834`; no other commit in `bfa2fd0..f3be834` touches a
module that existed at `bfa2fd0`, apart from the umbrella and `Axioms`). Six of them change
their line count: `DampedNorms` (372 to 373 lines), `DampedNormsHomog` (694
to 709), `SpatialFourierBound` (582 to 594), `SpatialOccupationCompleted`
(178 to 179), `SpatialSmoothRatio` (768 to 774) and `WaveGreen` (540 to
541). That moves only source positions, not kernel terms. The `.olean` files
were not compared byte for byte. All 35 passed default-mode replay at
`f3be834` in this job.

The 71 modules not replayed `--fresh` here were covered by earlier `--fresh`
replays. `harness/replay-coverage.py` is the wave-L6 script with two changes:
the wave-L6 replay (`bfa2fd0`, `leanchecker-easley-wave-l6`) is added as the
most recent entry of its list of earlier replays, and its docstring names the
wave-L7 job and `modules-wavel7.txt`. For each such module it takes the most
recent earlier Easley replay whose `summary.tsv` lists it with exit 0. It
checks that the module and every project module it imports have, with
comments stripped, the same source at that commit as at `f3be834`. All 71
pass (`harness/replay-coverage.txt`):

| Earlier `--fresh` replay | Folder | Byte-identical | Comment-only | Total |
|---|---|---|---|---|
| `bfa2fd0` | `leanchecker-easley-wave-l6` | 0 | 14 | 14 |
| `712c307` | `leanchecker-easley-wave-l5` | 0 | 7 | 7 |
| `2f5ee14` | `leanchecker-easley-wave-l4` | 2 (`MaskedModulation`, `TimeSchur`) | 13 | 15 |
| `687e631` | `leanchecker-easley-wave-l3` | 1 (`WeakSobolev`) | 1 (`GaussianIBP`) | 2 |
| `837778a` | `leanchecker-easley-2026-11-10` | 32 | 1 (`TemporalEquilibrium`) | 33 |

The 14 modules at `bfa2fd0` are the fourteen wave-L6 modules, and the 7 at
`712c307` are the seven wave-L5 modules; `harness/replay-coverage.txt` gives
the assignment module by module.
`closure-check.txt` contains the comparisons against all five commits
(`bfa2fd0`, `712c307`, `2f5ee14`, `687e631`, `837778a`). Relative to them it
finds 8, 22, 29, 36 and 46 new modules. Each comparison has 0 import-closure
gaps.

All 81 targets were replayed in default mode at `f3be834` in this job.

**Not covered.** The three comparator-tier Lake libraries `ChallengeDefs`,
`Challenge` and `Solution` are not imported by the umbrella and are not built
by `lake build StratonovichHAMSecondMoment`. This replay does not check them.
It also does not check the eleven wave-L8 modules added on main after
`f3be834` (`DampedMultiplier`, `FiniteWick`, `L8Completed`,
`OccupationCeilingFinite`, `RemoveMask`, `SpaceTimePositivity`,
`SpatialBracket`, `SpectralMassIdentity`, `StaticPhaseCauchy`,
`SymplecticFree`, `TerminalWick`), or the content changes that main later
made to the umbrella and `Axioms`.

## What was checked

| Item | Value |
|---|---|
| Commit | `f3be8348e28d0f050f8aa9896aaf029af8867b45` |
| Tree | `d32a656daa61a744a6be31ee551c895b031146ae` (checked inside the job, before the build and again after the replays) |
| Library sources vs later main | **different**: this replay certifies the sources at `f3be834` only. `git diff --stat f3be834 27d22a1 -- 'StratonovichHAM*' lakefile.toml lake-manifest.json lean-toolchain` lists 13 files, +8074 / -0 (`27d22a1` was origin/main when this folder was written). By `closure-check.py f3be834 27d22a1`: 11 new wave-L8 modules (above); the umbrella and `Axioms` changed in content (imports and `#print axioms` lines of the new modules); 0 modules changed only in comments; 79 byte-identical; none removed; 0 import-closure gaps. `lakefile.toml`, `lake-manifest.json` and `lean-toolchain` are identical. |
| Toolchain | `leanprover/lean4:v4.35.0`; Lean 4.35.0 (commit `eb6cafb7290e`), Lake 5.0.0 |
| Mathlib | `56a005855ea17e0b0958f73ec801ae140b0a1679`; the job checked this pin after `lake exe cache get` |
| `leanchecker` binary | sha256 `12c38901cdbfab178f1bf6145dd30012e9a3b2c11ca695292a5884fa3cbaddb6` (`lean` `bf8d54e4…`, `lake` `8ba83c98…`), the same binaries as in the wave-L5 and wave-L6 replays |
| Runtime | Lean 4.35.0 runtime tarball, extracted on the compute node, run inside the lab Apptainer image (Ubuntu 22.04, glibc 2.35) with `--cleanenv` |
| Host | Easley, partition `nova_20`, QOS `resourcecap_plus`; node831 |
| Build | `lake build StratonovichHAMSecondMoment StratonovichHAMSecondMoment.Axioms`: "Build completed successfully (9128 jobs)."; `ALL_OLEANS_PRESENT=81` |

The build log has 1899 `#print axioms` lines and no Lean warnings. Its only
other non-progress line is the Singularity `HOME` notice discussed below. 1886
declarations depend on `[propext, Classical.choice, Quot.sound]`, two on
`[propext, Quot.sound]`, two on `[propext]` and nine on no axioms. No
declaration depends on `sorryAx`. Only the tail is kept here
(`build.tail.log`).

## Commands

The private repository was cloned on the login node over GitHub ssh, and
`f3be8348e28d…` was checked out detached. The job copied that clone, without
`.lake`, to node-local `/tmp`. Inside the container, with
`PATH=<runtime>/bin:/usr/bin:/bin`, `LEAN_NUM_THREADS=3` and
`LAKE_ARTIFACT_CACHE=false`, it ran:

```
lake exe cache get
lake build StratonovichHAMSecondMoment StratonovichHAMSecondMoment.Axioms
timeout -k 30s 3600s  lake env leanchecker <Module>           # default mode, all 81 targets, serial
timeout -k 30s 14400s lake env leanchecker --fresh <Module>   # 10 targets, one process each, 2 at a time
```

Submitted with `sbatch --cpus-per-task=4 --mem=40G --time=1-00:00:00`.

Before building, the job also checked:
- the commit, tree and clean status;
- that the module list equals the source files plus the umbrella, and that
  the umbrella imports every module except `Axioms`;
- that the Mathlib pin is correct, and that no project `.olean` existed
  before the build.

After the build it checked that all 81 `.olean` files exist.

The harness is the wave-L6 one with three changes in `gate.sbatch`: the job
name (`stratham-l7-lchk`), and the commit and tree pins (with the header
comment that names the commit). After redaction, `diff` against the wave-L6
folder's `harness/gate.sbatch` shows only these lines. `replay.py` is
unchanged (same sha256 as in the wave-L5 and wave-L6 folders).
`modules-all.txt` equals the list of `StratonovichHAMSecondMoment` and
`StratonovichHAMAudit` source files at `f3be834` plus the umbrella (81
entries), and `modules-wavel7.txt` equals the 8 new modules plus the umbrella
and `Axioms` found by `closure-check.py bfa2fd0 f3be834`.

To avoid exceeding the node-wide open-file limit (262,144), the harness read
`/proc/sys/fs/file-nr` before the `--fresh` phase and would have dropped to
one run at a time above 60,000. It read 1,440 (`PRE_FRESH file-nr=1440
requested_par=2`), so two runs went ahead in parallel. `monitor.log` samples
`file-nr` and cgroup memory every 10 s (1,436 samples). The peak was 123,840
open files, at 06:31:26 node time during the first pair of runs. The cgroup
memory peak was 30.0 GB, page cache included, out of the 40G request.

The harness is in `harness/`. Those are redacted copies: the HPC username is
replaced by `<user>`, the container image path by `<container>.sif` and the
runtime tarball's scratch directory by `<runtime-dir>`. The hash of
`gate.sbatch` therefore differs from the original listed in
`harness/INPUT-SHA256SUMS`, which the job checked. `replay.py`,
`modules-all.txt` and `modules-wavel7.txt` contain none of these and match
their listed hashes (`sha256sum -c` reports OK for those three). The image has
no `/usr/bin/time`, so `replay.py` takes each run's peak RSS and CPU time
from `os.wait4` on that run's process. The `.time` files show `Job: NA`
because `--cleanenv` hides `SLURM_JOB_ID`. The job id is the last column of
`summary.tsv`.

Each `singularity exec` call prints `WARNING: Overriding HOME environment
variable with SINGULARITYENV_HOME is not permitted`. It appears 9 times in
`gate.log`, once in `cache-get-1.log` and once in the full build log, the
same counts as in the wave-L6 folder. The harness passes `HOME=$G/cache` in
the `--env` list. Singularity ignores this one entry, because `HOME` can only
be changed with `--home`, and keeps the container's default `HOME`. The
other entries apply, among them `XDG_CACHE_HOME=$G/cache` on node-local
`/tmp`, where the Mathlib cache is downloaded, and
`GIT_CONFIG_GLOBAL=/dev/null`. The job checked the commit, tree, Mathlib pin
and fresh build itself. `leanchecker --fresh` re-checks every declaration of
each target and of all its imports, wherever the `.olean` files came from.
The warning is harmless.

## Job (sacct)

| Job | State | Elapsed | TotalCPU | CPUs / ReqMem | MaxRSS (batch) | Node |
|---|---|---|---|---|---|---|
| 5692712 | COMPLETED 0:0 | 04:00:39 | 07:57:02 | 4 / 40G | 16,795,232 KB | node831 |

The job started at 2026-11-12 05:51:46 CST (06:51 EST) and ended at
2026-11-12 09:52:25 CST. Phases: `cache get` 101 s, build 358 s,
default-mode replay 852 s (81/81 pass), `--fresh` replay 13,078 s (10/10
pass). Each `--fresh` run took 43:22–44:03 with a 7.57–7.72 GB peak. The
total `--fresh` wall time over the 10 runs is 26,129 s.

## Files

- `summary.tsv`: one row per target, in the order of `modules-wavel7.txt`.
  Columns: module, exit code, wall time (h:mm:ss), peak RSS (KiB), output
  bytes, job id.
- `fresh-time/<Module>.time`: the record of each run.
- `default/summary-5692712.tsv`: the default-mode replay of all 81 targets.
- `jobs/5692712/`: `gate.log`, `monitor.log`, `runtime-preflight.log`,
  `runtime-binaries.sha256`, `cache-get-1.log`, and `build.tail.log` (the
  last 13 lines of the build log: the last four `#print axioms` messages and
  the completion line). In `gate.log` and `cache-get-1.log` the carriage
  returns of the cache-download progress line are replaced by newlines, as in
  the wave-L5 and wave-L6 folders.
- `harness/`: `gate.sbatch`, `replay.py`, `modules-all.txt`,
  `modules-wavel7.txt` and `INPUT-SHA256SUMS`, the inputs of the job.
  `closure-check.py` with its output `closure-check.txt`, and
  `replay-coverage.py` with its output `replay-coverage.txt`, are the
  target-selection checks above. They ran on a local checkout and were not
  part of the job.

The HPC username is redacted to `<user>`, the container image path to
`<container>.sif` and the runtime directory name to `<runtime-dir>` in every
file of this folder.
