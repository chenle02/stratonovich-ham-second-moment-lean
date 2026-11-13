# External kernel replay on Easley with `leanchecker --fresh` (2026-11-10)

This is an independent replay of commit `837778a` on Auburn's Easley cluster
(Slurm). It starts from a fresh clone and a fresh build. Each module is
replayed by its own `leanchecker --fresh` run, which also re-checks every
transitive import (Lean core, Batteries and the imported Mathlib slice), not
only the package's own declarations.
It complements the local default-mode replay in
`verification/leanchecker-2026-11-10/`, which trusted the imported `.olean`
files.

**Result.** All 35 targets pass `lake env leanchecker --fresh <Module>`: the
34 modules of `StratonovichHAMAudit` (24) and `StratonovichHAMSecondMoment`
(10, including `Axioms`), plus the umbrella `StratonovichHAMSecondMoment`.
Each exits 0 with empty output, which is the pass signature. Every row of
`summary.tsv` comes from a successful run and names the job that produced it.
Six targets first failed with an environment error (ENFILE, below) and passed
when rerun.

## What was checked

| Item | Value |
|---|---|
| Commit | `837778a7ce25b2c082025a8231c9c9b5c3828856` |
| Tree | `0cd15e0ebb9409b76a94e5ff29e83c05eab29a1d` (checked inside every job, before the build and again after the replays) |
| Toolchain | `leanprover/lean4:v4.35.0`; Lean 4.35.0 (commit `eb6cafb7290e`), Lake 5.0.0 |
| Mathlib | `56a005855ea17e0b0958f73ec801ae140b0a1679`; each job checked this pin after `lake exe cache get` |
| `leanchecker` binary | sha256 `12c38901cdbfab178f1bf6145dd30012e9a3b2c11ca695292a5884fa3cbaddb6` (from `jobs/*/runtime-binaries.sha256`) |
| Runtime | Lean 4.35.0 runtime tarball (sha256 `9bca7d29…ee18f`), extracted on the compute node, run inside the lab Apptainer image (Ubuntu 22.04, glibc 2.35) with `--cleanenv` |
| Host | Easley, partition `nova_20`, QOS `resourcecap_plus`; nodes node819, node807 and node841 |

**Later commits.** The library sources are byte-identical between `837778a`
and the later commits `9033c4e` and `64070a7`. Both commands below print
nothing:

```
git diff --stat 837778a 9033c4e -- '*.lean' lakefile.toml lake-manifest.json lean-toolchain
git diff --stat 837778a 64070a7 -- 'StratonovichHAM*' lakefile.toml lake-manifest.json lean-toolchain
```

Between those commits, the `refutations/` and `controls/` files changed. They
are not modules of the library and are not replayed here. **This replay does
not cover `4721cf9` or later.** Commit `4721cf9` adds 10 modules
(`ClockCopy`, `DampedNorms`, `FiniteGaussianMatrix`, `GaussianIBP`,
`IndexedCone`, `SpectralHomog`, `TimeFractional`, `VariationalDilation`,
`WaveKernel` and `WeakSobolev`) and changes the umbrella and `Axioms.lean`.

## Commands

The private repository was cloned on the login node with
`git clone git@github.com:chenle02/stratonovich-ham-second-moment-lean.git`
and the commit checked out with `git checkout --detach 837778a7ce25…`. Each
job copied that clone, without `.lake`, to node-local `/tmp`. Inside the
container, with `PATH=<runtime>/bin:/usr/bin:/bin`, `LEAN_NUM_THREADS=3` and
`LAKE_ARTIFACT_CACHE=false`, each job ran the following:

```
lake exe cache get
lake build StratonovichHAMSecondMoment StratonovichHAMSecondMoment.Axioms   # "Build completed successfully (9082 jobs)."
# for each target, one process per target:
timeout -k 30s 1800s  lake env leanchecker <Module>            # default mode, serial
timeout -k 30s 14400s lake env leanchecker --fresh <Module>    # PARALLEL processes at a time
```

Before building, each job also checked:
- the commit, tree and clean status;
- that the module list equals the source files plus the umbrella, and that
  the umbrella imports every module except `Axioms`;
- that no project `.olean` existed before the build, and that all 35
  `.olean` files existed after it.

`harness/` holds the exact scripts:
- `gate.sbatch` and `replay.py` were used by jobs 5685763 and 5685781.
- `gate.rerun.sbatch` and `replay.rerun.py` were used by job 5688166. They add
  the `rerun` mode, sample the monitor every 10 s, and fix the wall-time
  format.
- `gate.umbrella.sbatch` was used by job 5688359. It adds the `umbrella` mode.

The image has no `/usr/bin/time`, so `replay.py` takes each run's peak RSS
and CPU time from `os.wait4` on that run's process. Every `.time` file shows
`Job: NA` because `--cleanenv` hides `SLURM_JOB_ID` from the container. The
job is identified by the directory it is in and by the last column of
`summary.tsv`.

## Jobs (sacct)

| Job | Role | State | Elapsed | TotalCPU | CPUs / ReqMem | MaxRSS (batch) | Node |
|---|---|---|---|---|---|---|---|
| 5685751 | pilot, attempt 1 | FAILED 1:0 | 00:07:00 | 00:32.6 | 4 / 32G | 4.8 MB | node819 |
| 5685763 | pilot | COMPLETED 0:0 | 00:22:14 | 23:03 | 4 / 32G | 8,742,120 KB | node819 |
| 5685781 | all 35 `--fresh`, PARALLEL=6 | FAILED 7:0 | 01:42:25 | 06:53:27 | 7 / 64G | 20,487,956 KB | node807 |
| 5688166 | rerun of the 6 ENFILE targets, PARALLEL=1 | CANCELLED (deliberate) | 03:40:13 | 03:42:57 | 4 / 24G | 13,957,024 KB | node807 |
| 5688359 | umbrella `--fresh` only | FAILED 7:0 (default-mode sizing, below) | 01:25:39 | 53:58.8 | 4 / 16G | 15,484,664 KB | node841 |

**5685751.** The manifest check in my harness failed. A docstring line in
`StratonovichHAMSecondMoment.lean` begins "import a single …", and
`grep '^import '` counted "a" as a module. No Lean ran. The pattern became
`^import StratonovichHAM` and the pilot was resubmitted.

**5685763 (pilot).**
- Build: 151 s.
- Default-mode replay: 35/35 pass.
- `--fresh StratonovichHAMAudit.WhiteCDF`: exit 0, 627 s, 3.0 GB peak
  (`jobs/5685763/fresh-WhiteCDF.time`).
- The full run was sized from these numbers.

**5685781 (all targets).**
- Default mode: 35/35 pass (`default/summary-5685781.tsv`).
- `--fresh`: 29 targets passed. Six, all in `StratonovichHAMSecondMoment`,
  exited 1 after about 7 s with
  `uncaught exception: failed to open file '…/Mathlib/….olean.server': Too many open files in system`:
  `HomogHypothesis`, `MaskedTrigProducts`, `RadiusMeanAnchor`,
  `RayleighTail`, `TemporalEquilibrium` and the umbrella. They failed while
  opening Mathlib files, before any declaration was checked. This is ENFILE,
  the node-wide file-table limit, not a kernel rejection.
- One `--fresh` run of a module that imports the large Mathlib slice holds
  about 62–72k open files. Six such runs at once exceeded the 262,144 limit:
  `monitor.log` peaked at `file-nr` 258,800.
- The failing logs and `.time` files are kept in `enfile-failures-5685781/`.
  They are not merged into the summary.

**5688166 (rerun).**
- PARALLEL=1. `/proc/sys/fs/file-nr` was logged every 10 s and peaked at
  71,520 of 262,144.
- Default mode: 35/35 pass.
- `--fresh`: the five non-umbrella ENFILE targets each passed in about
  42 min with a 7.6 GB peak.
- To finish sooner, the umbrella was moved to job 5688359. I cancelled
  5688166 with `scancel` at 2026-11-10T20:46:01-06:00. That was after
  `TemporalEquilibrium` had finished (`END … 0 0:41:43.12`) and 20 s into its
  umbrella run. So 5688166 has no umbrella row, by design, and its gate log
  has no final `SOURCE_UNCHANGED_AFTER_GATE` line.

**5688359 (umbrella).**
- `--fresh StratonovichHAMSecondMoment`: exit 0, empty output, 46:21,
  7.7 GB peak. This is the umbrella row in `summary.tsv`.
- The job is FAILED because of a sizing problem in its default-mode pass. In
  default mode the umbrella needs about 14 GB RSS. With `--mem=16G` the cgroup
  sat at its 17,179,869,184-byte cap, and the run hit the 1800 s timeout
  (exit 124, no output).
- The record is in `default/StratonovichHAMSecondMoment-5688359-timeout.time`.
- This is not a kernel finding. The same default-mode umbrella replay passed
  in 5685763, 5685781 and 5688166, at 37 s and 13.9 GB in 5685781.
- After the replays, the job checked that the tree was unchanged
  (`SOURCE_UNCHANGED_AFTER_GATE`).

## Files

- `summary.tsv`: the merged `--fresh` result, one row per target. Columns:
  module, exit code, wall time (h:mm:ss), peak RSS (KiB), output bytes, job
  id. Wall times are recomputed from the raw seconds in each `.time` file.
  5685781's own summary printed two values as `0:11:60.00`, a rounding bug in
  its formatter. Their `.time` files record 720.00 s, which is 0:12:00.00.
- `fresh-time/<Module>.time`: the record of the successful run for each row.
- `default/summary-<job>.tsv`: the default-mode replays from each job. These
  are 35/35 in 5685763, 5685781 and 5688166, and 34/35 in 5688359 (the
  memory-cap timeout above).
- `enfile-failures-5685781/`: the six ENFILE logs and `.time` files.
- `jobs/<job>/`: `gate.log`, `monitor.log` (`file-nr` and cgroup memory),
  `runtime-preflight.log`, `runtime-binaries.sha256`, `cache-get-1.log` and
  the tail of the build log for each job.
- `harness/`: the scripts and the module list (`modules-all.txt`).

Total `--fresh` wall time over the 35 successful runs is 39,390 s, about
10.9 h of single-thread replay. Most `StratonovichHAMAudit` modules took
about 12 min at 3.0 GB. The two `HermiteWord*` modules took 2.5 min at
0.7 GB. Modules that import the larger Mathlib slice (`Axioms`,
`GaussianScalarPowers`, the five ENFILE reruns and the umbrella) took
42–46 min at 7.6 GB.

## Redaction

Before committing, the HPC username in absolute paths (`/home/...`,
`/scratch/...`) was replaced by `<user>` in the README, the gate logs and
the sbatch harness. Nothing else in these files was changed; the per-module
`.time` files and `summary.tsv` contained no such paths.
For the public release, the container image path was further replaced by `<container>.sif` and the name of the scratch directory holding the runtime tarball by `<runtime-dir>`.
