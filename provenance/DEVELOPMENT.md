# Development history and provenance

This repository starts from a single root commit. The companion was developed
in a separate repository, which stays private; this file says where that
history is, which development commit this release reproduces, and exactly what
changed between the two.

## Repositories

| Repository | Visibility | Contents |
|---|---|---|
| `chenle02/stratonovich-ham-second-moment-lean` (this one) | public | the release tree in one root commit; the commit after it, which adds only the receipts that bind the root commit; the release tag `v0.9.0` on that second commit |
| `chenle02/stratonovich-ham-second-moment-lean-dev` | private | the full development history (331 commits reachable from the commit below, and the wave branches), the milestone tags, and the receipts of every gated development commit |
| `chenle02/stratonovich-ham-second-moment` | to be published | the manuscript and the complete development history of the paper, including the record of the Lean work (`lean-progress/PROGRESS.md`) and the correspondence reviews (`reviews/`) |

The development history is not published here because its early commits
contain machine-local paths and account names that the release tree does not
need. Nothing in the release tree depends on that history.

## The development commit this release reproduces

| | Commit | Tree |
|---|---|---|
| final development commit | `34b65d78df5897c7c8dadd39e9f1c79e359ded20` | `6c993848cfd4835a014d6f81a08b3517c3b88bba` |
| verified commit (wave-L9 gate, tag `L9-gate`) | `6eb79c7b2ec4ca52f02121224484aa4865e43ac8` | `de6f79a14664bfad0e9c60dff29dc2f0ed37711e` |

`34b65d7` is a docs-only successor of `6eb79c7`: no build input (`*.lean`,
`lakefile.toml`, `lake-manifest.json`, `lean-toolchain`, `claims.yaml`,
`lean-pkg-binding.yaml`) changed between them. The development receipts of
`6eb79c7` are `.lean-receipts/6eb79c7b2ec4-*`.

Every commit hash cited in `README.md`, `COMPLETION.md`,
`docs/statement-ledger.md`, `verification/` and in the file names of the
receipts already in `.lean-receipts/` is a commit of the development
repository. Those 31 receipts (19 lower-tier, 12 comparator, with their logs,
for 20 development commits) are kept as development evidence; they do not bind
any commit of this repository. A receipt names the commit it binds, so the
receipts for this repository's root commit are not in the root commit itself:
they are added by the commit after it, and are the files whose 12-hex prefix
is the root commit (`git rev-list --max-parents=0 HEAD`).

## Milestone tags

The milestone tags are annotated tags in the development repository. This
repository carries only the release tag `v0.9.0`.

| Tag (development repository) | Commit |
|---|---|
| `L0-companion-created` | `38d1616` |
| `ledger-gate` | `48ce162` |
| `L1-gate` | `b876362` |
| `L2-gate` | `79afdde` |
| `L3-gate` | `dfc2fe8` |
| `L4-gate` | `ac6f767` |
| `reanchor-975feb3` | `d40f394` |
| `L5-gate` | `712c307` |
| `L6-gate` | `bfa2fd0` |
| `L7-gate` | `f3be834` |
| `L8-gate` | `aff7409` |
| `L9-gate` | `6eb79c7` |

`COMPLETION.md` gives the date, manuscript revision and counts of each.

## What differs from the tree of `34b65d7`

**Lean sources and statement files: nothing.** All 1147 `.lean` files are
byte-identical to `34b65d7` (checked mechanically: equal bytes, and equal token
streams with comments removed, with a positive control that detects a one-token
code change and a negative control that ignores a comment-only change). So are
`lakefile.toml`, `lake-manifest.json`, `lean-toolchain`, `claims.yaml`,
`coverage.yaml`, `comparator.json`, `Challenge.lean`, `Solution.lean` and every
file under `ChallengeDefs/`.

**Redactions in `verification/`** (cluster evidence; no Lean file). The
placeholders `<user>` and `<USER>` (in every folder) and `<container>.sif`
and `<runtime-dir>` (in the folders of wave L5 onward and in the Slurm receipt
pilot) were already in the development repository; the release adds only the
following:

1. The absolute path of the container image in the job scripts of the first
   three Easley replays is replaced by `<container>.sif` (5 files:
   `verification/leanchecker-easley-2026-11-10/harness/gate.sbatch`,
   `gate.rerun.sbatch`, `gate.umbrella.sbatch`,
   `verification/leanchecker-easley-wave-l3/harness/gate.sbatch`,
   `verification/leanchecker-easley-wave-l4/harness/gate.sbatch`).
2. The name of the scratch directory that held the runtime tarball, which was
   named after another project, is replaced by `<runtime-dir>` (the same 5
   scripts and 7 job logs `jobs/*/gate.log` of the same three folders).
3. The READMEs of those three folders say so in one added sentence. The
   `INPUT-SHA256SUMS` files of the wave-L3 and wave-L4 folders record the
   hashes of the original job inputs, as before; their READMEs already said
   that the published harness files are redacted copies.
4. A compiled Python cache file,
   `verification/leanchecker-easley-wave-l7/harness/__pycache__/closure-check.cpython-312.pyc`,
   committed by mistake, is removed (it held a local absolute path; the
   source `closure-check.py` is unchanged).
5. The name of a local workstation is replaced by `<MACHINE>` in 5 files
   (`verification/leanchecker-easley-wave-l8/harness/make-inputs.sh`,
   `verification/leanchecker-easley-wave-l9/harness/make-inputs.sh`, and in
   `verification/leanchecker-easley-wave-l9/d8-pilot/`: `inputs/pilot.sbatch`,
   `inputs/collect.py`, `collect-out.txt`), in comments and in one printed
   message; the wave-L8 and wave-L9 READMEs say so in one added sentence.
   The hashes of `pilot.sbatch` and `collect.py` in
   `d8-pilot/inputs/INPUT-SHA256SUMS` are those of the originals.

The HPC username was already redacted to `<user>` in the development
repository. The cluster stays named (Easley).

**Release documentation:** `README.md` restructured for a public reader (its
statements about what is and is not checked, the counts, the review record and
the verification record are unchanged, except that the no-`sorry` and axiom
statements now say that they concern the proof library and that
`Challenge.lean`, the comparator's statement file, states each compared
theorem with `sorry` by design; an "At a glance" table, a release section, a
milestone table copied from `COMPLETION.md` and pointers to this file were
added); one sentence in `COMPLETION.md` on where the milestone tags are; `CITATION.cff` (version `0.9.0`, release date, the paper as a
reference); `.zenodo.json` (archive metadata) and this file are new.

## Versions

`v0.9.0` is the wave-L9 gate. Waves L10 to L14 are in development (see the
"In progress" section of `COMPLETION.md`) and are not part of this release.
`v1.0.0` is planned after those waves are gated and the ledger is re-anchored
to the final manuscript revision. The Lake package version in `lakefile.toml`
is still `0.1.0`: the lakefile is a build input and is left exactly as
verified.
