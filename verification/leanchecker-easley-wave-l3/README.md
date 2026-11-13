# External kernel replay on Easley, wave L3 (`leanchecker --fresh`, 2026-11-11)

This is an independent replay of commit `687e631` on Auburn's Easley cluster
(Slurm). It starts from a fresh clone and a fresh build, and checks the wave-L3
modules that the 837778a replay
(`verification/leanchecker-easley-2026-11-10/`) did not cover. Each target is
replayed by its own `lake env leanchecker --fresh <Module>` run, which also
re-checks every transitive import (Lean core, Batteries and the imported
Mathlib slice).

**Result.** All 12 targets exit 0 with empty output, which is the pass
signature. The job completed with one attempt and no failures.

## Covered modules

The ten modules new in wave L3:

- `StratonovichHAMSecondMoment.ClockCopy`
- `StratonovichHAMSecondMoment.DampedNorms`
- `StratonovichHAMSecondMoment.FiniteGaussianMatrix`
- `StratonovichHAMSecondMoment.GaussianIBP`
- `StratonovichHAMSecondMoment.IndexedCone`
- `StratonovichHAMSecondMoment.SpectralHomog`
- `StratonovichHAMSecondMoment.TimeFractional`
- `StratonovichHAMSecondMoment.VariationalDilation`
- `StratonovichHAMSecondMoment.WaveKernel`
- `StratonovichHAMSecondMoment.WeakSobolev`

Two targets that changed after `837778a`:

- `StratonovichHAMSecondMoment.Axioms`
- the umbrella `StratonovichHAMSecondMoment`

**Not covered by this replay:**
- The other 33 modules are byte-identical to `837778a`. Their `--fresh`
  replay is in `verification/leanchecker-easley-2026-11-10/`, and they passed
  default-mode replay in this job.
- Commits after `687e631` change library sources. In particular `2f5ee14`
  (wave L4) edits `ClockCopy`, `FiniteGaussianMatrix`, `IndexedCone`,
  `TimeFractional`, `VariationalDilation`, `Axioms` and the umbrella, so this
  replay does not certify those modules at `2f5ee14`. `DampedNorms`,
  `SpectralHomog` and `WaveKernel` have unchanged source but import the
  changed `TimeFractional`, so they too were replayed again at `2f5ee14`.
  The wave-L4 replay is in `verification/leanchecker-easley-wave-l4/`.

Default-mode replay, which re-checks only the named module's own
declarations, ran in the same job for all 44 modules plus the umbrella.
Result: 45/45 pass (`default/summary-5688396.tsv`).

## What was checked

| Item | Value |
|---|---|
| Commit | `687e631b1e9056bc3aa073d167b594b1dac0d29f` (origin/main at submission) |
| Tree | `e0d1e4419988c82e7f7dc82f7113971ae35a2d84` (checked inside the job, before the build and again after the replays) |
| Library sources vs `4721cf9` | identical: `git diff --stat 4721cf9 687e631 -- 'StratonovichHAM*' lakefile.toml lake-manifest.json lean-toolchain` prints nothing |
| Toolchain | `leanprover/lean4:v4.35.0`; Lean 4.35.0 (commit `eb6cafb7290e`), Lake 5.0.0 |
| Mathlib | `56a005855ea17e0b0958f73ec801ae140b0a1679`; the job checked this pin after `lake exe cache get` |
| `leanchecker` binary | sha256 `12c38901cdbfab178f1bf6145dd30012e9a3b2c11ca695292a5884fa3cbaddb6` (`lean` `bf8d54e4…`, `lake` `8ba83c98…`) |
| Runtime | Lean 4.35.0 runtime tarball, extracted on the compute node, run inside the lab Apptainer image (Ubuntu 22.04, glibc 2.35) with `--cleanenv` |
| Host | Easley, partition `nova_20`, QOS `resourcecap_plus`, node807 |
| Build | `lake build StratonovichHAMSecondMoment StratonovichHAMSecondMoment.Axioms`: "Build completed successfully (9092 jobs)." |

## Commands

The private repository was cloned on the login node over GitHub ssh, and
`687e631b1e90…` was checked out detached. The job copied that clone, without
`.lake`, to node-local `/tmp`. Inside the container, with
`PATH=<runtime>/bin:/usr/bin:/bin`, `LEAN_NUM_THREADS=3` and
`LAKE_ARTIFACT_CACHE=false`, it ran:

```
lake exe cache get
lake build StratonovichHAMSecondMoment StratonovichHAMSecondMoment.Axioms
timeout -k 30s 3600s  lake env leanchecker <Module>           # default mode, all 45 targets, serial
timeout -k 30s 14400s lake env leanchecker --fresh <Module>   # the 12 targets, one process each, 2 at a time
```

Before building, the job also checked:
- the commit, tree and clean status;
- that the module list equals the source files plus the umbrella, and that
  the umbrella imports every module except `Axioms`;
- that the Mathlib pin is correct, and that no project `.olean` existed
  before the build.

After the build, a loop checked that every module's `.olean` exists and is
non-empty. Its summary line prints `ALL_OLEANS_PRESENT=` without a number
because of a quoting bug in the count expression. The loop exits on the first
missing file, so the line is printed only after all 45 files were found.

At most two `--fresh` runs ran at once. A single run holds about 62–72k open
files, and the node-wide limit is 262,144. `monitor.log` samples
`/proc/sys/fs/file-nr` and the job's cgroup memory every 10 s. The peak was
123,520 open files.

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
| 5688396 | COMPLETED 0:0 | 04:35:16 | 09:01:43 | 4 / 40G | 14,754,640 KB | node807 |

Phases: `cache get` 141 s, build 204 s, default-mode replay 416 s, `--fresh`
replay 15,708 s. Each `--fresh` run took 43:07–44:04 with a 7.57–7.68 GB
peak. The total `--fresh` wall time over the 12 runs is 31,347 s.

## Files

- `summary.tsv`: one row per target. Columns: module, exit code, wall time
  (h:mm:ss), peak RSS (KiB), output bytes, job id.
- `fresh-time/<Module>.time`: the record of each run.
- `default/summary-5688396.tsv`: the default-mode replay of all 45 targets.
- `jobs/5688396/`: `gate.log`, `monitor.log`, `runtime-preflight.log`,
  `runtime-binaries.sha256`, `cache-get-1.log`, `build.tail.log`.
- `harness/`: `gate.sbatch`, `replay.py`, `modules-all.txt`,
  `modules-wavel3.txt`, `INPUT-SHA256SUMS`.

The HPC username is redacted to `<user>` in every file of this folder. For the public release, the container image path was further replaced by `<container>.sif` and the name of the scratch directory holding the runtime tarball by `<runtime-dir>`.
