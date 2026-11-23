# Development history and provenance

This repository holds the public releases of the companion. It starts from a
single root commit (release `v0.9.0`); each later release is one commit on
top of the previous history, followed by one commit that adds only the
receipts binding it. The companion is developed in a separate repository,
which stays private; this file says where that history is, which development
commit each release reproduces, and exactly what changed between the two.

## Repositories

| Repository | Visibility | Contents |
|---|---|---|
| `chenle02/stratonovich-ham-second-moment-lean` (this one) | public | per release: the release tree in one commit and the commit after it, which adds only the receipts that bind the release tree commit; the release tag marks that commit or a documentation-only descendant of it (`v0.9.0`, `v0.10.0`, `v0.11.0`); documentation-only commits in between |
| `chenle02/stratonovich-ham-second-moment-lean-dev` | private | the full development history (754 commits reachable from the `v0.11.0` development commit below, and the wave branches), the milestone tags, and the receipts of every gated development commit |
| `chenle02/stratonovich-ham-second-moment` | public (history rewritten; its `history/commit-map.tsv` maps original revisions to public commits) | the manuscript and the complete development history of the paper, including the record of the Lean work (`lean-progress/PROGRESS.md`) and the correspondence reviews (`reviews/`) |

The development history is not published here because its early commits
contain machine-local paths and account names that the release tree does not
need. Nothing in the release tree depends on that history.

## The development commit release `v0.11.0` reproduces

| | Commit | Tree |
|---|---|---|
| release development commit (branch `reanchor-edf7085f`) | `9534f89104ff8a6fe31c9ba3eb29f70a4b6bca2c` | `efed8b16de5604e033b4b1b55897fe4b58662a5a` |
| verified commit (wave L21, tag `L21-gate`) | `38a3e00f9fc70b847b442c658ba1dc2d47b462fc` | `4c9c0b2119e8f4bf79a7c3a1439b66416f8aef50` |

The two files `COMPLETION.md` and `provenance/manuscript-anchor.json` follow
development commit `037e181`, a documentation-only successor of `9534f89`
(wording from the final confirmation review of the re-anchor).

The release development commit is the wave-L21 gate commit `38a3e00` (waves
L15 to L21 on top of `v0.10.0`'s development commit, each gate with its
receipts, its Easley evidence and its gate record) with the 22 commits from
`38a3e00` to `9534f89` on top:

- The comment-only documentation repairs deferred from the wave-L21 reviews
  (module notes and docstrings of `MildInterface`, `EnvelopeFinal`,
  `CameronProducts` and `WickFinal`, and the `ChallengeDefs/` mirror of one
  of them), the comment-only repairs of the re-anchor review and its
  confirmation (docstrings; a private library name in two module docstrings
  reworded), and `claims.yaml` summaries reworded (summary text only), with
  their copies in the comparator scaffold and `Challenge.lean`.
- The re-anchor to manuscript revision `edf7085f` (book 1.1.3): the
  citations of waves up to L14 were at `39f2597a` and those of waves L15 to
  L21 at `0788ddee` (book 1.1.0). No TeX line number moved; only the revision
  labels next to the citations changed, in the comments of `.lean` files, in
  the documentation, in `coverage.yaml`, `docs/coverage-scope-tex.yaml`, the
  `claims.yaml` summaries and the comparator scaffold, with the anchor
  recorded in `provenance/manuscript-anchor.json`. The `.lean` changes are in
  comments only (checked mechanically: equal token streams with comments
  removed, all 3502 `.lean` files, 480 changed in comments, none in code).
  The re-anchor tooling (`reanchor/`) and `.gitattributes` are marked
  `export-ignore` in the development repository and are not part of this
  tree.

`lakefile.toml`, `lake-manifest.json` and `lean-toolchain` are unchanged
since `v0.10.0`. This repository's receipts for `v0.11.0` bind its own
release tree commit; the development receipts of the gate commits of waves
L15 to L21 are kept in `.lean-receipts/` as evidence.

## What the `v0.11.0` tree changes from the development commit

**Not exported: the interface records of waves L15 to L20**
(`docs/l15/INTERFACE.md` to `docs/l20/INTERFACE.md`). They are the working
notes the waves were built from (frozen signatures, the build commands of the
development machines and the readings decided for each item). Some module
docstrings and the statement ledger name them as design records; they are
files of the development repository. Everything they fixed that a reader
needs is in the Lean statements, their docstrings and the statement ledger.

**Lean sources and statement files: nothing.** All 3502 `.lean` files are
byte-identical to the release development commit (checked mechanically:
equal bytes). So are `lakefile.toml`, `lake-manifest.json`,
`lean-toolchain`, `claims.yaml`, `coverage.yaml` (in the release tree
commit), `comparator.json`, `comparator-helpers.json`,
`lean-pkg-signoff.json`, `Challenge.lean`, `Solution.lean` and every file
under `ChallengeDefs/`.

**Redactions in `verification/`**, as for `v0.10.0` (the five items below
apply unchanged to the folders they name); the folders of waves L15 to L21
(`verification/leanchecker-easley-wave-l15/` to `-wave-l21/`) have the
workstation name replaced by `<MACHINE>` in `harness/make-inputs.sh`
(comments) and in the README (the connection path to the login node), and
the READMEs say so in one added sentence.

**Other placeholders** (no Lean file): the name of a local workstation in
`COMPLETION.md` (`<MACHINE>`, in the build notes of the wave table); a path
to a private review record in the statement ledger (replaced by "its
adjudication record"); and, in `provenance/manuscript-anchor.json`, the
personal first name in the file name of one figure, now
`<person>-observatory-drawing.tex`, in the new revision entry as in the
earlier one (the recorded SHA-256 is that of the original file).

**Release documentation:** `README.md` keeps the public structure of
`v0.10.0`, with the text of the development commit merged into it (the
statements about what is and is not checked, the counts, the review record
and the verification record); the "At a glance" table, the release section,
the milestone table copied from `COMPLETION.md` and the receipt paragraph
are updated for `v0.11.0`. In `COMPLETION.md`, the sentence on where the
milestone tags are. `coverage.yaml` pins the posted manuscript: the book's release 1.1.3
(tag `v1.1.3` of the book repository, commit `4fa7e18a5b6d`, with the
SHA-256 of the book PDF there), whose TeX files are byte-identical to those
of `edf7085f`. `CITATION.cff` and `.zenodo.json` carry version `0.11.0`.
`.lean-pkg-public-allow` adds the harness folders of waves L15 to L21, whose
pinned inputs name the development repository.

## The development commit release `v0.10.0` reproduces

| | Commit | Tree |
|---|---|---|
| release development commit (branch `reanchor-39f2597a`) | `09cfc11a771a45f51506ef4efeda9667b7ded143` | `284887c1e5dd7a175b0607e5ba0fbb5ba255b33f` |
| its first part, the release bookkeeping (branch `release/v0.10.0-l14`) | `8df39cd633483e5fd82a3e17acbb16a635c605c2` | `3b3fa5fa3d468d3cdd9107bd426f4e9434f2aebc` |
| verified commit (waves L13 and L14, tags `L13-gate` and `L14-gate`) | `8f51004c412ac618f4be6a5f4a42c7cc78188638` | `79a7f16872b7c49a7055b032451460e2f9af3f0d` |

The two documentation files `README.md` and `docs/statement-ledger.md` follow
development commit `402b646`, a documentation-only successor of `09cfc11`
(wording from the confirmation review of the re-anchor).

The release development commit is development main `e9f7bf6` (the gate
commit `8f51004` with its receipts, its Easley evidence and its gate record)
with the following on top (all but the last item are `8df39cd`; the last is
the 20 commits from `8df39cd` to `09cfc11`):

- Two claims that named declarations generated by Lean are dropped from
  `claims.yaml`, the statement ledger, `comparator.json` and the comparator
  scaffold: `WhiteFour.tacticTw_close` (the syntax constant of a local
  tactic macro) and `MaskedAuxiliaryReal.Cx.ext_iff` (generated by
  `@[ext]`); `Challenge.lean` and `Solution.lean`, regenerated by
  `scripts/comparator/gen_cs.py`, lose that one theorem and nothing else.
- `comparator.json` keeps the 1553 compared theorems that are the
  declarations of claims a `coverage.yaml` row names (1134 named at the
  gate, 419 credited by the direct-label rule); the other 2100 moved to
  `comparator-helpers.json`, which the new file `lean-pkg-signoff.json`
  declares a smoke check (compared, credited to no result). Together they
  hold the 3653 theorem claims.
- `coverage.yaml`: 433 claim ids appended to the `claims` lists of 52 rows,
  a header comment, and one note that names its manuscript file without its
  directory (lean-pkg's page refuses such a path); no class,
  scope, input or other note changed.
- `claims.yaml`: 491 claims of the helper configuration changed status from
  `reusable` to `internal` (status lines only), among them 18
  structure-field projections (of `EndpointLemmas` and `ClassOBridge`)
  that lean-pkg 0.29.0 cannot match to their claims.
- `scripts/comparator/CheckFidelity.lean`, `CopySpans.lean` and `gen_cs.py`
  read both configurations (`CheckFidelity`: 3653 of 3653 restatement types
  equal, 0 problems; `gen_cs.py` regenerates `Challenge.lean` and
  `Solution.lean` byte-identical).
- Documentation: the counts and the comparator accounting in `README.md`,
  `FORMALIZATION.md` and `docs/statement-ledger.md`.
- The re-anchor to manuscript revision `39f2597a`, the release revision of
  the manuscript: every TeX line locator moved to that revision in the
  comments of `.lean` files (the proof library, `ChallengeDefs/`,
  `Challenge.lean`, `Solution.lean`, `Audit/`, `refutations/` and
  `scripts/`), in `docs/statement-ledger.md`, `COMPLETION.md`,
  `FORMALIZATION.md`, `coverage.yaml`, `docs/coverage-scope-tex.yaml`, the
  `claims.yaml` summaries and `scripts/comparator/scaffold.json`, with the
  anchor recorded in `provenance/manuscript-anchor.json` and the
  manuscript's new title in `README.md` and `coverage.yaml`; TeX locators
  already wrong at `a284420` corrected (`2487458` and during the re-anchor);
  the appendix-local direct-bound constant written `C_dir` (`1220baf`); two
  documentation corrections in `coverage.yaml` (`e415c36`). The `.lean` changes are in
  comments only (checked mechanically: equal token streams with comments
  removed). The re-anchor tooling (`reanchor/`) and `.gitattributes` are
  marked `export-ignore` in the development repository and are not part of
  this tree.

No Lean file of the proof library and no `ChallengeDefs/` file differs from
`8f51004` except in comments (the re-anchor); `lakefile.toml`, `lake-manifest.json` and `lean-toolchain` are
unchanged. The development receipts of `8f51004`
(`.lean-receipts/8f51004c412a-*`) judged the 3654 theorem claims of that
commit in one configuration; this repository's receipts for `v0.10.0` bind
its own release tree commit and judge the two configurations.

The release `v0.9.0` reproduced development commit
`34b65d78df5897c7c8dadd39e9f1c79e359ded20`, a docs-only successor of the
wave-L9 gate `6eb79c7b2ec4ca52f02121224484aa4865e43ac8`.

Every commit hash cited in `README.md`, `COMPLETION.md`,
`docs/statement-ledger.md`, `verification/` and in the file names of the
development receipts in `.lean-receipts/` is a commit of the development
repository. Those 149 files (31 lower-tier and 24 comparator receipts with
their logs, for 32 development commits) are kept as development evidence;
they do not bind any commit of this repository. A receipt names the commit
it binds, so the receipts of a release tree commit are added by the commit
after it: for `v0.9.0` the files whose 12-hex prefix is the root commit, for
`v0.10.0` and `v0.11.0` the files whose 12-hex prefix is the parent of the
commit that adds them (`c8d8e0706afb` and `4d0e11cec4f6`).

## Milestone tags

The milestone tags are annotated tags in the development repository. This
repository carries only the release tags `v0.9.0`, `v0.10.0` and `v0.11.0`.

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
| `L10-gate` | `b2bf7a9` |
| `L11-gate` | `b780f10` |
| `L12-gate` | `56fc59e` |
| `L13-gate` | `8f51004` |
| `L14-gate` | `8f51004` |
| `L15-gate` | `18c5c1d` |
| `L16-gate` | `ebac849` |
| `L17-gate` | `68d0c5e` |
| `L18-gate` | `6e4644d` |
| `L19-gate` | `fe9f1de` |
| `L20-gate` | `5cdd493` |
| `L21-gate` | `38a3e00` |

`COMPLETION.md` gives the date, manuscript revision and counts of each.

## What the `v0.10.0` tree changed from its development commit

**Lean sources and statement files: nothing.** All 1997 `.lean` files are
byte-identical to the release development commit (checked mechanically:
equal bytes, and equal token streams with comments removed, with a positive
control that detects a one-token code change and a negative control that
ignores a comment-only change). So are `lakefile.toml`, `lake-manifest.json`,
`lean-toolchain`, `claims.yaml`, `coverage.yaml`, `comparator.json`,
`comparator-helpers.json`, `lean-pkg-signoff.json`, `Challenge.lean`,
`Solution.lean` and every file under `ChallengeDefs/`.

**Redactions in `verification/`** (cluster evidence; no Lean file). The
placeholders `<user>` and `<USER>` (in every folder) and `<container>.sif`
and `<runtime-dir>` (in the folders of wave L5 onward and in the Slurm receipt
pilots) are already in the development repository; the release adds only the
following, as for `v0.9.0`:

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
   hashes of the original job inputs, as before.
4. A compiled Python cache file,
   `verification/leanchecker-easley-wave-l7/harness/__pycache__/closure-check.cpython-312.pyc`,
   committed by mistake, is removed (it held a local absolute path; the
   source `closure-check.py` is unchanged).
5. The name of a local workstation is replaced by `<MACHINE>` in 14 files:
   `harness/make-inputs.sh` of the wave-L8 to wave-L12 folders and of
   `verification/leanchecker-easley-wave-l13-l14/` (comments), the READMEs of
   the wave-L10, L11, L12 and L13-L14 folders (the connection path to the
   login node), and in `verification/leanchecker-easley-wave-l9/d8-pilot/`:
   `inputs/pilot.sbatch`, `inputs/collect.py`, `inputs/expect.tsv` and
   `collect-out.txt` (comments, one printed message, and the column label
   of the comparison timings, also in lower case). The READMEs of those
   folders from wave L8 on say so in one added sentence. The hashes of
   `pilot.sbatch`, `collect.py` and `expect.tsv` in
   `d8-pilot/inputs/INPUT-SHA256SUMS` are those of the originals.

**Redaction in `provenance/manuscript-anchor.json`** (the record of the
manuscript revision; no Lean file). In the file name of one figure of the
manuscript, now `<person>-observatory-drawing.tex`, a personal first name
is replaced by `<person>`; the recorded SHA-256 is that of the original
file.

The HPC username was already redacted to `<user>` in the development
repository. The cluster stays named (Easley).

**Release documentation:** `README.md` restructured for a public reader as
for `v0.9.0` (its statements about what is and is not checked, the counts,
the review record and the verification record are those of the development
commit, except that the no-`sorry` and axiom statements say that they
concern the proof library and that `Challenge.lean`, the comparator's
statement file, states each compared theorem with `sorry` by design; an "At
a glance" table, a release section, a milestone table copied from
`COMPLETION.md` and pointers to this file are added); in `COMPLETION.md`, one
sentence on where the milestone tags are; `CITATION.cff` (version `0.10.0`, release date, Zenodo DOIs,
the paper as a reference); `.zenodo.json` (archive metadata),
`.lean-pkg-public-allow`, `site/` (the documentation site sources) and this
file exist only in this repository. The public receipts of `v0.9.0`'s root
commit (`.lean-receipts/ed66b5bc05fe-*`) stay.

## Versions

`v0.9.0` is the wave-L9 gate. `v0.10.0` is the wave-L13 and wave-L14 gates
with the bookkeeping changes above, and re-anchors every manuscript line
citation to the manuscript's release revision `39f2597a`. `v0.11.0` is the
wave-L15 to wave-L21 gates, the end point of the Lean work, and re-anchors
every manuscript line citation to `edf7085f` (book 1.1.3). A later `v1.0.0`
is planned once the manuscript is posted, so that the companion can cite its
public version. The Lake package
version in `lakefile.toml` is still `0.1.0`: the lakefile is a build input
and is left exactly as verified.
