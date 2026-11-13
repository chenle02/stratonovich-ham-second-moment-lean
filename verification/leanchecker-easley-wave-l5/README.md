# External kernel replay on Easley, wave L5 (`leanchecker --fresh`, 2026-11-11)

This is an independent replay of commit `712c307` on Auburn's Easley cluster
(Slurm). `712c307` is the commit at which the wave-L5 review gate closed
(the author accepted the wave-L5 correspondence reviews at `712c307`, as
recorded in the README at `a7f90b0`). The job started from a fresh
clone and a fresh build. Each target is replayed by its own
`lake env leanchecker --fresh <Module>` run, which also re-checks every
transitive import (Lean core, Batteries and the imported Mathlib slice).

**Result.** All 9 targets exit 0 with empty output, which is the pass signature. The job completed with one attempt and no failures.

All 59 targets (58 modules plus the umbrella) also passed default-mode
replay in this job (`default/summary-5690458.tsv`).

## Covered modules

The seven modules new in wave L5:

- `StratonovichHAMSecondMoment.TimeCompletion`
- `StratonovichHAMSecondMoment.MaskedContinuousWave`
- `StratonovichHAMSecondMoment.MaskedContinuousWaveCompleted`
- `StratonovichHAMSecondMoment.MaskedAuxiliaryNorm`
- `StratonovichHAMSecondMoment.DampedNormsHomog`
- `StratonovichHAMSecondMoment.VariationalMean`
- `StratonovichHAMSecondMoment.PhaseBessel`

Two targets whose source changed in content after the wave-L4 replay commit
`2f5ee14`:

- the umbrella `StratonovichHAMSecondMoment` (imports of the seven new
  modules);
- `StratonovichHAMSecondMoment.Axioms` (`#print axioms` lines for them).

### Import-closure check

`harness/closure-check.py` reads both commits with `git show` only. For each
library module it strips the Lean comments (`/- -/`, nested, which covers doc
comments and module docs, and `--` line comments; string and character
literals are kept) and compares the result at `712c307` with the source at an
earlier commit. It then computes each module's transitive project imports at
`712c307` and lists every unchanged module that imports a new or changed one.
Its output is in `harness/closure-check.txt`.

Relative to `2f5ee14` it finds 7 new modules, 2 changed in content (the
umbrella and `Axioms`), 14 changed only in comments and 36 byte-identical. No
module was removed, and no unchanged module imports a new or changed one: the
seven new modules are imported only by the umbrella, and the umbrella only by
`Axioms`.

The 14 comment-only modules are the TeX line-number updates of the re-anchor
to manuscript revision `975feb3` (commits `d9e5ce9` and `d40f394`):
- `ClockCopy`, `ClockCopyHomog`, `DampedNorms`, `FiniteGaussianMatrix`,
  `FrequencyRow`, `GaussianIBP`, `GaussianTest`, `IndexedCone`;
- `MaskedSpectralGrowth`, `OccupationKernelRow`, `SpectralHomog`,
  `TemporalEquilibrium`, `TimeFractional`, `WaveKernel`.

Their line counts are unchanged too, so no declaration moved to another line.
Their `.olean` files at `712c307` should differ from the replayed ones only in
docstrings; the `.olean` files were not compared byte for byte. These 14 were
not replayed `--fresh` again. Each has, with comments stripped, the same
source as at the commit of its earlier `--fresh` replay, and the same holds
for every project module it imports:
- 12 at `2f5ee14`, in `verification/leanchecker-easley-wave-l4/`;
- `GaussianIBP` at `687e631`, in `verification/leanchecker-easley-wave-l3/`;
- `TemporalEquilibrium` at `837778a`, in
  `verification/leanchecker-easley-2026-11-10/`.

`closure-check.txt` contains the comparisons against all three commits.

The 36 byte-identical modules were covered by earlier `--fresh` replays, as
recorded in `verification/leanchecker-easley-wave-l4/`:
- 32 at `837778a` (byte-identical to `837778a` as well);
- `WeakSobolev` at `687e631`;
- `MaskedModulation`, `TimeSchur` and `VariationalDilation` at `2f5ee14`.

All 59 targets were replayed in default mode at `712c307` in this job.

**Not covered.** As at `2f5ee14`, the three comparator-tier Lake libraries
`ChallengeDefs`, `Challenge` and `Solution` are not imported by the umbrella,
are not built by `lake build StratonovichHAMSecondMoment`, and are not
checked by this replay.

## What was checked

| Item | Value |
|---|---|
| Commit | `712c3075703d373825c306711000027d401286fe` |
| Tree | `ecafe71bfb1c8ba7b31ed306f751af991a8be55c` (checked inside the job, before the build and again after the replays) |
| Library sources vs later main | identical. `git diff --stat 712c307 a7f90b0 -- 'StratonovichHAM*' lakefile.toml lake-manifest.json lean-toolchain` prints nothing (`a7f90b0` was origin/main when this folder was written). |
| Toolchain | `leanprover/lean4:v4.35.0`; Lean 4.35.0 (commit `eb6cafb7290e`), Lake 5.0.0 |
| Mathlib | `56a005855ea17e0b0958f73ec801ae140b0a1679`; the job checked this pin after `lake exe cache get` |
| `leanchecker` binary | sha256 `12c38901cdbfab178f1bf6145dd30012e9a3b2c11ca695292a5884fa3cbaddb6` (`lean` `bf8d54e4…`, `lake` `8ba83c98…`), the same binaries as in the wave-L4 replay |
| Runtime | Lean 4.35.0 runtime tarball, extracted on the compute node, run inside the lab Apptainer image (Ubuntu 22.04, glibc 2.35) with `--cleanenv` |
| Host | Easley, partition `nova_20`, QOS `resourcecap_plus`; node831 |
| Build | `lake build StratonovichHAMSecondMoment StratonovichHAMSecondMoment.Axioms`: "Build completed successfully (9106 jobs)."; `ALL_OLEANS_PRESENT=59` |

## Commands

The private repository was cloned on the login node over GitHub ssh, and
`712c3075703d…` was checked out detached. The job copied that clone, without
`.lake`, to node-local `/tmp`. Inside the container, with
`PATH=<runtime>/bin:/usr/bin:/bin`, `LEAN_NUM_THREADS=3` and
`LAKE_ARTIFACT_CACHE=false`, it ran:

```
lake exe cache get
lake build StratonovichHAMSecondMoment StratonovichHAMSecondMoment.Axioms
timeout -k 30s 3600s  lake env leanchecker <Module>           # default mode, all 59 targets, serial
timeout -k 30s 14400s lake env leanchecker --fresh <Module>   # 9 targets, one process each, 2 at a time
```

Before building, the job also checked:
- the commit, tree and clean status;
- that the module list equals the source files plus the umbrella, and that
  the umbrella imports every module except `Axioms`;
- that the Mathlib pin is correct, and that no project `.olean` existed
  before the build.

After the build it checked that all 59 `.olean` files exist.

The harness is the wave-L4 one with three changes in `gate.sbatch`: the job
name (`stratham-l5-lchk`) and the commit and tree pins. `replay.py` is
unchanged (same sha256 as in the wave-L4 folder).

To avoid exceeding the node-wide open-file limit (262,144), the harness read
`/proc/sys/fs/file-nr` before the `--fresh` phase and would have dropped to
one run at a time above 60,000. It read 1,360, so two runs went ahead in
parallel. `monitor.log` samples `file-nr` and cgroup memory every 10 s. The
peak was 123,640 open files.

The harness is in `harness/`. Those are redacted copies: the HPC username is
replaced by `<user>`, the container image path by `<container>.sif` and the
runtime tarball's scratch directory by `<runtime-dir>`, so the
hash of `gate.sbatch` differs from the original listed in
`harness/INPUT-SHA256SUMS`, which the job checked. `replay.py`,
`modules-all.txt` and `modules-wavel5.txt` contain neither and match their
listed hashes. The image has no `/usr/bin/time`, so `replay.py` takes each
run's peak RSS and CPU time from `os.wait4` on that run's process. The `.time`
files show `Job: NA` because `--cleanenv` hides `SLURM_JOB_ID`. The job id is
the last column of `summary.tsv`.

## Job (sacct)

| Job | State | Elapsed | TotalCPU | CPUs / ReqMem | MaxRSS (batch) | Node |
|---|---|---|---|---|---|---|
| 5690458 | COMPLETED 0:0 | 03:51:54 | 06:57:04 | 4 / 40G | 15,641,784 KB | node831 |

Phases: `cache get` 87 s, build 244 s, default-mode replay 579 s (59/59
pass), `--fresh` replay 12,929 s. Each `--fresh` run took
41:41–43:52 with a 7.57–7.69 GB peak. The total `--fresh` wall
time over the 9 runs is 23,387 s.

## Files

- `summary.tsv`: one row per target. Columns: module, exit code, wall time
  (h:mm:ss), peak RSS (KiB), output bytes, job id.
- `fresh-time/<Module>.time`: the record of each run.
- `default/summary-5690458.tsv`: the default-mode replay of all 59 targets.
- `jobs/5690458/`: `gate.log`, `monitor.log`, `runtime-preflight.log`,
  `runtime-binaries.sha256`, `cache-get-1.log`, `build.tail.log`.
- `harness/`: `gate.sbatch`, `replay.py`, `modules-all.txt`,
  `modules-wavel5.txt` and `INPUT-SHA256SUMS`, the inputs of the job; and
  `closure-check.py` with its output `closure-check.txt`, the target-selection
  check above (run on a local checkout, not part of the job).

The HPC username is redacted to `<user>`, the container image path to
`<container>.sif` and the runtime directory name to `<runtime-dir>` in every
file of this folder.
