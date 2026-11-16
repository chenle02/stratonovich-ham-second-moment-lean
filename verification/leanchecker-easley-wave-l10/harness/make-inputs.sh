#!/usr/bin/env bash
# LOCAL (laptop/<MACHINE>). Freeze the inputs of one L11 Easley array campaign.
#
# usage: make-inputs.sh COMPANION_DIR COMMIT OUT_DIR [FRESH_SET]
#   FRESH_SET = all (default: every manifest target --fresh)
#             | new:<BASE_COMMIT> (only modules new or changed vs BASE, plus umbrella and Axioms;
#               the rest then needs the replay-coverage argument of the wave-L6 folder)
#
# Reads the commit with `git show`/`git ls-tree` only (never checks out). Writes into OUT_DIR:
#   pins.env            commit, tree, Mathlib rev, runtime/container paths and hashes
#   modules-all.txt     LC_ALL=C-sorted library modules, then the umbrella (format of waves L3-L7)
#   targets-fresh.txt   one --fresh target per line; array task i (1-based) replays line i
#   the harness scripts (copied) and INPUT-SHA256SUMS over everything.
# Precondition (CLAUDE.md HPC rule 1): COMMIT already builds locally (lake build of the umbrella and
# Axioms on <MACHINE> or the laptop) and its lean-pkg receipts exist. Easley is the gate, not the compiler.
set -euo pipefail
[ "$#" -ge 3 ] || { sed -n '2,15p' "$0"; exit 64; }
C=$(cd -- "$1" && pwd -P); COMMIT=$(git -C "$C" rev-parse --verify "$2^{commit}"); OUT=$3; SET=${4:-all}
HERE=$(cd -- "$(dirname -- "$0")" && pwd -P)
TREE=$(git -C "$C" rev-parse "$COMMIT^{tree}")
mkdir -- "$OUT"
mods_at() {  # library modules at a commit, sorted, then the umbrella
  git -C "$C" ls-tree -r --name-only "$1" -- StratonovichHAMAudit StratonovichHAMSecondMoment \
    | grep '\.lean$' | sed 's/\.lean$//; s#/#.#g' | LC_ALL=C sort
  echo StratonovichHAMSecondMoment
}
mods_at "$COMMIT" > "$OUT/modules-all.txt"
case "$SET" in
  all) cp -- "$OUT/modules-all.txt" "$OUT/targets-fresh.txt" ;;
  new:*)
    BASE=$(git -C "$C" rev-parse --verify "${SET#new:}^{commit}")
    { git -C "$C" diff --name-only "$BASE" "$COMMIT" -- StratonovichHAMAudit StratonovichHAMSecondMoment \
        | grep '\.lean$' | sed 's/\.lean$//; s#/#.#g'
      echo StratonovichHAMSecondMoment; echo StratonovichHAMSecondMoment.Axioms; } \
      | LC_ALL=C sort -u | grep -x -F -f "$OUT/modules-all.txt" > "$OUT/targets-fresh.txt" ;;
  *) echo "bad FRESH_SET $SET" >&2; exit 64 ;;
esac
# no duplicate targets; every target in the manifest
[ "$(sort "$OUT/targets-fresh.txt" | uniq -d | wc -l)" = 0 ]
grep -v -x -F -f "$OUT/modules-all.txt" "$OUT/targets-fresh.txt" && { echo 'target outside manifest' >&2; exit 65; } || true
MATHLIB_REV=$(git -C "$C" show "$COMMIT:lake-manifest.json" \
  | python3 -I -c 'import json,sys; print([p["rev"] for p in json.load(sys.stdin)["packages"] if p["name"]=="mathlib"][0])')
[ "$(git -C "$C" show "$COMMIT:lean-toolchain")" = 'leanprover/lean4:v4.35.0' ] || { echo 'toolchain is not v4.35.0: new runtime tarball needed' >&2; exit 66; }
cat > "$OUT/pins.env" <<EOF
# Sourced by the Easley scripts after INPUT-SHA256SUMS passes. Paths are Easley paths.
EXPECTED_COMMIT=$COMMIT
EXPECTED_TREE=$TREE
MATHLIB_REV=$MATHLIB_REV
RUNTIME_SHA=9bca7d29b89503da3ce0e015000ff7aa425788b93814adf3e34e5a4792fee18f
SIF=<container>.sif
TB=/scratch/<user>/<runtime-dir>/lean-4.35.0-runtime.tar.gz
SINGULARITY=/tools/singularity-3.8.4/bin/singularity
TOOLDIR=leanprover--lean4---v4.35.0
GITHUB_REPO=git@github.com:chenle02/stratonovich-ham-second-moment-lean.git
FILE_NR_MAX=190000
EOF
for f in stage-login.sh preflight-login.sh build.sbatch task.sbatch submit.sh collect.py replay.py; do
  cp -- "$HERE/$f" "$OUT/$f"
done
(cd "$OUT" && sha256sum pins.env modules-all.txt targets-fresh.txt stage-login.sh preflight-login.sh \
   build.sbatch task.sbatch submit.sh collect.py replay.py > INPUT-SHA256SUMS)
echo "INPUTS commit=$COMMIT tree=$TREE mathlib=$MATHLIB_REV modules=$(wc -l < "$OUT/modules-all.txt") fresh_targets=$(wc -l < "$OUT/targets-fresh.txt")"
echo "Next: copy $OUT to Easley as /scratch/<user>/stratham-l11-${COMMIT:0:7}/inputs (see L11-DRAFT.md, section A3)."
