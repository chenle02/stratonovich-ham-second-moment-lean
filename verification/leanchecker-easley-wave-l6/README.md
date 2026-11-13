# External kernel replay on Easley, wave L6 (`leanchecker --fresh`, 2026-11-11)

This is an independent replay of commit `bfa2fd0` on Auburn's Easley cluster
(Slurm). `bfa2fd0` is the commit at which the wave-L6 correspondence gate
closed (the author closed it on 2026-11-11, as recorded in the README at
`e4c9bd4`). The job started from a fresh clone and a fresh build. Each target
is replayed by its own `lake env leanchecker --fresh <Module>` run, which also
re-checks every transitive import (Lean core, Batteries and the imported
Mathlib slice).

**Result.** All 16 targets exit 0 with empty output, which is the pass
signature. The job completed with one attempt and no failures.

All 73 targets (72 modules plus the umbrella) also passed default-mode
replay in this job (`default/summary-5692528.tsv`).

## Covered modules

The fourteen modules new in wave L6:

- `StratonovichHAMSecondMoment.WaveGreen`
- `StratonovichHAMSecondMoment.QuotientObstruction`
- `StratonovichHAMSecondMoment.GaussianComparison`
- `StratonovichHAMSecondMoment.WaveTwoVariances`
- `StratonovichHAMSecondMoment.SpatialFourierBound`
- `StratonovichHAMSecondMoment.VariationalFloor`
- `StratonovichHAMSecondMoment.VariationalRate`
- `StratonovichHAMSecondMoment.SpatialSmoothRatio`
- `StratonovichHAMSecondMoment.SpatialStaticControls`
- `StratonovichHAMSecondMoment.SpatialOccupationCompleted`
- `StratonovichHAMSecondMoment.SeriesType`
- `StratonovichHAMSecondMoment.TypeContinuity`
- `StratonovichHAMSecondMoment.WhiteRelativeWidth`
- `StratonovichHAMSecondMoment.WhiteClockLaplace`

Two targets whose source changed in content after the wave-L5 replay commit
`712c307`:

- the umbrella `StratonovichHAMSecondMoment` (imports of the fourteen new
  modules);
- `StratonovichHAMSecondMoment.Axioms` (`#print axioms` lines for them).

### Import-closure check

`harness/closure-check.py` is the wave-L5 script, copied unchanged (same
sha256 as in `verification/leanchecker-easley-wave-l5/harness/`). It reads
both commits with `git show` only. For each library module it strips the Lean
comments (`/- -/`, nested, which covers doc comments and module docs, and
`--` line comments; string and character literals are kept) and compares the
result at `bfa2fd0` with the source at an earlier commit. It then computes
each module's transitive project imports at `bfa2fd0` and lists every
unchanged module that imports a new or changed one. Its output is in
`harness/closure-check.txt`.

Relative to `712c307` it finds 14 new modules, 2 changed in content (the
umbrella and `Axioms`), 2 changed only in comments and 55 byte-identical. No
module was removed, and no unchanged module imports a new or changed one: the
fourteen new modules are imported only by the umbrella, and the umbrella only
by `Axioms`.

The 2 comment-only modules are `DampedNorms` and `DampedNormsHomog`. Their doc
comments now say that the wave Green measures are not defined in that module
and point to `WaveGreen` (commits `89cea2f` and `4b09ee6`, review finding W3
and confirmation C1). `DampedNorms` keeps its line count. `DampedNormsHomog`
gains two lines (one in the module doc, one in the docstring of `GreenMass`),
so its declarations after line 50 sit one or two lines lower than at
`712c307`. That moves only source positions, not kernel terms. The `.olean`
files were not compared byte for byte. Both modules passed default-mode
replay at `bfa2fd0` in this job.

The 57 modules not replayed `--fresh` here were covered by earlier `--fresh`
replays. `harness/replay-coverage.py` (new in this folder; it reuses the
comment stripping and import parsing of `closure-check.py`) takes, for each
such module, the most recent earlier Easley replay whose `summary.tsv` lists
it with exit 0. It checks that the module and every project module it imports
have, with comments stripped, the same source at that commit as at `bfa2fd0`.
All 57 pass (`harness/replay-coverage.txt`):

| Earlier `--fresh` replay | Folder | Byte-identical | Comment-only | Total |
|---|---|---|---|---|
| `712c307` | `leanchecker-easley-wave-l5` | 6 | 1 (`DampedNormsHomog`) | 7 |
| `2f5ee14` | `leanchecker-easley-wave-l4` | 3 | 12 | 15 |
| `687e631` | `leanchecker-easley-wave-l3` | 1 (`WeakSobolev`) | 1 (`GaussianIBP`) | 2 |
| `837778a` | `leanchecker-easley-2026-11-10` | 32 | 1 (`TemporalEquilibrium`) | 33 |

The 12 comment-only modules at `2f5ee14` are the ones listed in the wave-L5
README (the TeX line-number updates of the re-anchor to manuscript revision
`975feb3`), with `DampedNorms` among them. Since `712c307`, `DampedNorms` has
also changed in the comments described above. `closure-check.txt` contains the
comparisons against all four commits (`712c307`, `2f5ee14`, `687e631`,
`837778a`). Relative to them it finds 14, 21, 28 and 38 new modules. Each
comparison has 0 import-closure gaps.

All 73 targets were replayed in default mode at `bfa2fd0` in this job.

**Not covered.** The three comparator-tier Lake libraries `ChallengeDefs`,
`Challenge` and `Solution` are not imported by the umbrella and are not built
by `lake build StratonovichHAMSecondMoment`. This replay does not check them.
It also does not check the eight wave-L7 modules added on main after
`bfa2fd0` (`H1Density`, `IntervalScalar`, `IntervalScalarCompleted`,
`InventoryProduct`, `OccupationPhysicalClass`, `SpatialFourLinear`,
`SpatialOccupationL7Completed`, `UniformSeriesTail`), or the content changes
that main later made to the umbrella and `Axioms`.

## What was checked

| Item | Value |
|---|---|
| Commit | `bfa2fd0ed721aa7bd2fc027a15b787d5024f4d57` |
| Tree | `8bd4a1e93a5fa13d3c0fac340cea9c7872f48ffc` (checked inside the job, before the build and again after the replays) |
| Library sources vs later main | **different**: this replay certifies the sources at `bfa2fd0` only. `git diff --stat bfa2fd0 47f3af4 -- 'StratonovichHAM*' lakefile.toml lake-manifest.json lean-toolchain` lists 45 files, +6751 / -374 (`47f3af4` was origin/main when this folder was written). By `closure-check.py bfa2fd0 47f3af4`: 8 new wave-L7 modules (above); the umbrella and `Axioms` changed in content (imports and `#print axioms` lines of the new modules); 35 modules changed only in comments; 36 byte-identical; none removed; 0 import-closure gaps. `lakefile.toml`, `lake-manifest.json` and `lean-toolchain` are identical. |
| Toolchain | `leanprover/lean4:v4.35.0`; Lean 4.35.0 (commit `eb6cafb7290e`), Lake 5.0.0 |
| Mathlib | `56a005855ea17e0b0958f73ec801ae140b0a1679`; the job checked this pin after `lake exe cache get` |
| `leanchecker` binary | sha256 `12c38901cdbfab178f1bf6145dd30012e9a3b2c11ca695292a5884fa3cbaddb6` (`lean` `bf8d54e4…`, `lake` `8ba83c98…`), the same binaries as in the wave-L5 replay |
| Runtime | Lean 4.35.0 runtime tarball, extracted on the compute node, run inside the lab Apptainer image (Ubuntu 22.04, glibc 2.35) with `--cleanenv` |
| Host | Easley, partition `nova_20`, QOS `resourcecap_plus`; node831 |
| Build | `lake build StratonovichHAMSecondMoment StratonovichHAMSecondMoment.Axioms`: "Build completed successfully (9120 jobs)."; `ALL_OLEANS_PRESENT=73` |

The build log has 1620 `#print axioms` lines and no Lean warnings. Its only
other non-progress line is the Singularity `HOME` notice discussed below. 1609
declarations depend on `[propext, Classical.choice, Quot.sound]`, one on
`[propext, Quot.sound]`, two on `[propext]` and eight on no axioms. No
declaration depends on `sorryAx`. Only the tail is kept here
(`build.tail.log`).

## Commands

The private repository was cloned on the login node over GitHub ssh, and
`bfa2fd0ed721…` was checked out detached. The job copied that clone, without
`.lake`, to node-local `/tmp`. Inside the container, with
`PATH=<runtime>/bin:/usr/bin:/bin`, `LEAN_NUM_THREADS=3` and
`LAKE_ARTIFACT_CACHE=false`, it ran:

```
lake exe cache get
lake build StratonovichHAMSecondMoment StratonovichHAMSecondMoment.Axioms
timeout -k 30s 3600s  lake env leanchecker <Module>           # default mode, all 73 targets, serial
timeout -k 30s 14400s lake env leanchecker --fresh <Module>   # 16 targets, one process each, 2 at a time
```

Submitted with `sbatch --cpus-per-task=4 --mem=40G --time=1-00:00:00`.

Before building, the job also checked:
- the commit, tree and clean status;
- that the module list equals the source files plus the umbrella, and that
  the umbrella imports every module except `Axioms`;
- that the Mathlib pin is correct, and that no project `.olean` existed
  before the build.

After the build it checked that all 73 `.olean` files exist.

The harness is the wave-L5 one with three changes in `gate.sbatch`: the job
name (`stratham-l6-lchk`), and the commit and tree pins (with the header
comment that names the commit). After redaction, `diff` against the wave-L5
folder's `harness/gate.sbatch` shows only these lines. `replay.py` is
unchanged (same sha256 as in the wave-L5 folder).

To avoid exceeding the node-wide open-file limit (262,144), the harness read
`/proc/sys/fs/file-nr` before the `--fresh` phase and would have dropped to
one run at a time above 60,000. It read 1,400 (`PRE_FRESH file-nr=1400
requested_par=2`), so two runs went ahead in parallel. `monitor.log` samples
`file-nr` and cgroup memory every 10 s (2,197 samples). The peak was 123,800
open files, at 21:58:04 node time during the first pair of runs. The cgroup
memory peak was 30.3 GB, page cache included, out of the 40G request.

The harness is in `harness/`. Those are redacted copies: the HPC username is
replaced by `<user>`, the container image path by `<container>.sif` and the
runtime tarball's scratch directory by `<runtime-dir>`. The hash of
`gate.sbatch` therefore differs from the original listed in
`harness/INPUT-SHA256SUMS`, which the job checked. `replay.py`,
`modules-all.txt` and `modules-wavel6.txt` contain none of these and match
their listed hashes (`sha256sum -c` reports OK for those three). The image has
no `/usr/bin/time`, so `replay.py` takes each run's peak RSS and CPU time
from `os.wait4` on that run's process. The `.time` files show `Job: NA`
because `--cleanenv` hides `SLURM_JOB_ID`. The job id is the last column of
`summary.tsv`.

Each `singularity exec` call prints `WARNING: Overriding HOME environment
variable with SINGULARITYENV_HOME is not permitted`. It appears 9 times in
`gate.log`, once in `cache-get-1.log` and once in the full build log. The wave-L5 folder has the same counts in
`gate.log` and `cache-get-1.log`. The harness passes `HOME=$G/cache` in the
`--env` list. Singularity ignores this one entry, because `HOME` can only be
changed with `--home`, and keeps the container's default `HOME`. The other
entries apply, among them `XDG_CACHE_HOME=$G/cache` on node-local `/tmp`,
where the Mathlib cache is downloaded, and `GIT_CONFIG_GLOBAL=/dev/null`. The
warning does not affect the result. The job checked the commit, tree, Mathlib
pin and fresh build itself. `leanchecker --fresh` re-checks every declaration
of each target and of all its imports, wherever the `.olean` files came from.
The warning is harmless.

## Job (sacct)

| Job | State | Elapsed | TotalCPU | CPUs / ReqMem | MaxRSS (batch) | Node |
|---|---|---|---|---|---|---|
| 5692528 | COMPLETED 0:0 | 06:09:54 | 12:14:46 | 4 / 40G | 16,441,652 KB | node831 |

The job started at 2026-11-11 20:57:20 CST (21:57 EST) and ended at
2026-11-12 03:06:56 CST. Phases: `cache get` 88 s, build 319 s, default-mode
replay 794 s (73/73 pass), `--fresh` replay 20,925 s (16/16 pass). Each
`--fresh` run took 43:13–44:08 with a 7.57–7.71 GB peak. The total `--fresh`
wall time over the 16 runs is 41,796 s.

## Files

- `summary.tsv`: one row per target, in the order of `modules-wavel6.txt`.
  Columns: module, exit code, wall time (h:mm:ss), peak RSS (KiB), output
  bytes, job id.
- `fresh-time/<Module>.time`: the record of each run.
- `default/summary-5692528.tsv`: the default-mode replay of all 73 targets.
- `jobs/5692528/`: `gate.log`, `monitor.log`, `runtime-preflight.log`,
  `runtime-binaries.sha256`, `cache-get-1.log`, and `build.tail.log` (the
  last 13 lines of the build log: the last four `#print axioms` messages and
  the completion line). In `gate.log` and `cache-get-1.log` the carriage
  returns of the cache-download progress line are replaced by newlines, as in
  the wave-L5 folder.
- `harness/`: `gate.sbatch`, `replay.py`, `modules-all.txt`,
  `modules-wavel6.txt` and `INPUT-SHA256SUMS`, the inputs of the job.
  `closure-check.py` with its output `closure-check.txt`, and
  `replay-coverage.py` with its output `replay-coverage.txt`, are the
  target-selection checks above. They ran on a local checkout and were not
  part of the job.

The HPC username is redacted to `<user>`, the container image path to
`<container>.sif` and the runtime directory name to `<runtime-dir>` in every
file of this folder.
