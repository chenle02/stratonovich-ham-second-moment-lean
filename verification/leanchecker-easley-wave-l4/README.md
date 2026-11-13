# External kernel replay on Easley, wave L4 (`leanchecker --fresh`, 2026-11-11)

This is an independent replay of commit `2f5ee14` on Auburn's Easley cluster
(Slurm). `2f5ee14` is the commit with both lean-pkg receipts for wave L4. Each
of the two jobs started from a fresh clone and a fresh build. Each target is
replayed by its own `lake env leanchecker --fresh <Module>` run, which also
re-checks every transitive import (Lean core, Batteries and the imported
Mathlib slice).

**Result.** All 17 targets exit 0 with empty output, which is the pass
signature:
- 14 targets in job 5688553;
- 3 targets in the follow-up job 5688619 (see "Import-closure check" below).

Both jobs completed with one attempt each and no failures.

## Covered modules

The seven modules new in wave L4:

- `StratonovichHAMSecondMoment.ClockCopyHomog`
- `StratonovichHAMSecondMoment.FrequencyRow`
- `StratonovichHAMSecondMoment.GaussianTest`
- `StratonovichHAMSecondMoment.MaskedModulation`
- `StratonovichHAMSecondMoment.MaskedSpectralGrowth`
- `StratonovichHAMSecondMoment.OccupationKernelRow`
- `StratonovichHAMSecondMoment.TimeSchur`

Seven targets whose source changed after the wave-L3 replay commit `687e631`:

- `StratonovichHAMSecondMoment.Axioms`
- the umbrella `StratonovichHAMSecondMoment`
- `StratonovichHAMSecondMoment.ClockCopy`
- `StratonovichHAMSecondMoment.FiniteGaussianMatrix`
- `StratonovichHAMSecondMoment.IndexedCone`
- `StratonovichHAMSecondMoment.TimeFractional`
- `StratonovichHAMSecondMoment.VariationalDilation`

The last five were not in the requested target list. The list called them
covered by earlier replays, but `git diff --stat 687e631 2f5ee14` shows edits
to each of them (7–31 lines). Their `.olean` files at `2f5ee14` therefore
differ from the ones the wave-L3 replay checked, so they are replayed here.

### Import-closure check (job 5688619)

A module whose own source is unchanged can still have a different `.olean`
if a module it imports changed. For every library module I compared, at
`2f5ee14` and at the commit of its earlier replay, the Git blob of the module
and of every project module it imports, directly or indirectly. Three modules
are byte-identical to `687e631` but import `TimeFractional`, which changed:
- `DampedNorms`
- `SpectralHomog`
- `WaveKernel`

The follow-up job 5688619 replayed these three with `--fresh` at `2f5ee14`.
That makes 17 targets replayed at `2f5ee14`.

The remaining 35 library modules have the same source as at the commit of
their earlier `--fresh` replay, and so do all the project modules they
import:
- 33 at `837778a`, in `verification/leanchecker-easley-2026-11-10/`;
- `GaussianIBP` and `WeakSobolev` at `687e631`, in
  `verification/leanchecker-easley-wave-l3/`.

The same check found no gap in the wave-L3 coverage relative to `837778a`.

All 52 targets (51 modules plus the umbrella) also passed default-mode replay
in this job (`default/summary-5688553.tsv`).

**Not covered.** `2f5ee14` adds three Lake libraries for the comparator tier:
`ChallengeDefs`, `Challenge` and `Solution`. The umbrella does not import
them, `lake build StratonovichHAMSecondMoment` does not build them, and this
replay does not check them.

## What was checked

| Item | Value |
|---|---|
| Commit | `2f5ee14ff24714ca275b8febc5838f9a15fc8df9` |
| Tree | `a054dfa0d47e5e65a7e8bc87671c3497a28779cb` (checked inside the job, before the build and again after the replays) |
| Library sources vs later main | identical. `git diff --stat 2f5ee14 68fa364 -- 'StratonovichHAM*' lakefile.toml lake-manifest.json lean-toolchain` prints nothing, and so does the same diff against `4a66a69` (origin/main when this folder was written). |
| Toolchain | `leanprover/lean4:v4.35.0`; Lean 4.35.0 (commit `eb6cafb7290e`), Lake 5.0.0 |
| Mathlib | `56a005855ea17e0b0958f73ec801ae140b0a1679`; the job checked this pin after `lake exe cache get` |
| `leanchecker` binary | sha256 `12c38901cdbfab178f1bf6145dd30012e9a3b2c11ca695292a5884fa3cbaddb6` (`lean` `bf8d54e4…`, `lake` `8ba83c98…`) |
| Runtime | Lean 4.35.0 runtime tarball, extracted on the compute node, run inside the lab Apptainer image (Ubuntu 22.04, glibc 2.35) with `--cleanenv` |
| Host | Easley, partition `nova_20`, QOS `resourcecap_plus`; node841 (5688553) and node807 (5688619) |
| Build | `lake build StratonovichHAMSecondMoment StratonovichHAMSecondMoment.Axioms`: "Build completed successfully (9099 jobs)."; `ALL_OLEANS_PRESENT=52` |

## Commands

The private repository was cloned on the login node over GitHub ssh, and
`2f5ee14ff247…` was checked out detached. The job copied that clone, without
`.lake`, to node-local `/tmp`. Inside the container, with
`PATH=<runtime>/bin:/usr/bin:/bin`, `LEAN_NUM_THREADS=3` and
`LAKE_ARTIFACT_CACHE=false`, it ran:

```
lake exe cache get
lake build StratonovichHAMSecondMoment StratonovichHAMSecondMoment.Axioms
timeout -k 30s 3600s  lake env leanchecker <Module>           # default mode, all 52 targets, serial
timeout -k 30s 14400s lake env leanchecker --fresh <Module>   # 14 targets (5688553) and 3 targets (5688619), one process each, 2 at a time
```

Before building, the job also checked:
- the commit, tree and clean status;
- that the module list equals the source files plus the umbrella, and that
  the umbrella imports every module except `Axioms`;
- that the Mathlib pin is correct, and that no project `.olean` existed
  before the build.

After the build it checked that all 52 `.olean` files exist.

This job ran while the wave-L3 job 5688396 was also running. To avoid
exceeding the node-wide open-file limit (262,144), the harness read
`/proc/sys/fs/file-nr` before the `--fresh` phase and would have dropped to
one run at a time above 60,000. It read 1,272: the job was on a different
node (node841) from the L3 job (node807), so two runs went ahead in
parallel. `monitor.log` samples `file-nr` and cgroup memory every 10 s. The
peak was 123,552 open files.

The harness is in `harness/`. Those are redacted copies: the HPC username is
replaced by `<user>`, so their hashes differ from the originals listed in
`harness/INPUT-SHA256SUMS`, which the job checked. The image has no
`/usr/bin/time`, so `replay.py` takes each run's peak RSS and CPU time from
`os.wait4` on that run's process. The `.time` files show `Job: NA` because
`--cleanenv` hides `SLURM_JOB_ID`. The job id is the last column of
`summary.tsv`.

## Job (sacct)

| Job | State | Elapsed | TotalCPU | CPUs / ReqMem | MaxRSS (batch) | Node |
|---|---|---|---|---|---|---|
| 5688553 | COMPLETED 0:0 | 05:18:32 | 10:29:28 | 4 / 40G | 15,485,864 KB | node841 |
| 5688619 | COMPLETED 0:0 | 01:40:08 | 02:31:38 | 4 / 40G | 16,345,468 KB | node807 |

**5688553.** Phases: `cache get` 124 s, build 245 s, default-mode replay
524 s (52/52 pass), `--fresh` replay 18,167 s. Each `--fresh` run took
42:46–43:45 with a 7.57–7.68 GB peak.

**5688619.** Phases: `cache get` 137 s, build 234 s ("Build completed
successfully (9099 jobs)."), default-mode replay 495 s (52/52 pass),
`--fresh` replay 5,098 s. The three runs took 41:44–43:40 with a 7.57 GB
peak. `file-nr` read 1,360 before the `--fresh` phase and peaked at 123,240.
The job checked the commit and tree before the build, and the tree again
after the replays.

The total `--fresh` wall time over the 17 runs is 44,007 s.

## Files

- `summary.tsv`: one row per target. Columns: module, exit code, wall time
  (h:mm:ss), peak RSS (KiB), output bytes, job id.
- `fresh-time/<Module>.time`: the record of each run.
- `default/summary-<job>.tsv`: the default-mode replay of all 52 targets in
  each job.
- `jobs/<job>/`: `gate.log`, `monitor.log`, `runtime-preflight.log`,
  `runtime-binaries.sha256`, `cache-get-1.log`, `build.tail.log`.
- `harness/`: `gate.sbatch`, `replay.py` and `modules-all.txt`, the same
  files for both jobs. Also `modules-wavel4.txt` (5688553),
  `modules-wavel4b.txt` (5688619), `INPUT-SHA256SUMS` (5688553) and
  `INPUT-SHA256SUMS-5688619`.

The HPC username is redacted to `<user>` in every file of this folder. For the public release, the container image path was further replaced by `<container>.sif` and the name of the scratch directory holding the runtime tarball by `<runtime-dir>`.
