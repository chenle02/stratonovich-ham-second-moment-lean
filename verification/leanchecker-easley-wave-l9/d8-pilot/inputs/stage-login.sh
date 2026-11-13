#!/usr/bin/env bash
# EASLEY LOGIN NODE. Clone the private companion at the pinned commit into RUN_DIR/src (no .lake); the job
# uses it only for lean-toolchain, lakefile and lake-manifest (Mathlib pin) and runs `lake exe cache get`.
# usage: stage-login.sh RUN_DIR
set -euo pipefail
R=$(cd -- "${1:?RUN_DIR}" && pwd -P); IN=$R/inputs
(cd "$IN" && sha256sum -c --quiet INPUT-SHA256SUMS)
# shellcheck disable=SC1091
. "$IN/pins.env"
for name in GIT_DIR GIT_WORK_TREE GIT_INDEX_FILE GIT_COMMON_DIR GIT_OBJECT_DIRECTORY GIT_ALTERNATE_OBJECT_DIRECTORIES; do unset "$name"; done
test ! -e "$R/src"
git clone --quiet --no-checkout "$GITHUB_REPO" "$R/src" < /dev/null
git -C "$R/src" -c advice.detachedHead=false checkout --quiet --detach "$EXPECTED_COMMIT"
git -C "$R/src" config gc.auto 0; git -C "$R/src" config maintenance.auto false
test "$(git -C "$R/src" rev-parse HEAD)" = "$EXPECTED_COMMIT"
test "$(git -C "$R/src" rev-parse 'HEAD^{tree}')" = "$EXPECTED_TREE"
test -z "$(git -C "$R/src" status --porcelain --ignored)"
test ! -e "$R/src/.lake"
mkdir -p "$R/slurm-out"
echo "STAGED $R/src at $EXPECTED_COMMIT (clean, no .lake)"
