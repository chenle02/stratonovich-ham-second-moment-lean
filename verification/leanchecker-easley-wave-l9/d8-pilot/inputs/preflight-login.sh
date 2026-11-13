#!/usr/bin/env bash
# EASLEY LOGIN NODE. Preflight before the single sbatch (CLAUDE.md HPC rule 2): every tool the job calls,
# inside the job's image, with --cleanenv and the job's own PATH line, checked with `type -P`.
# Writes RUN_DIR/PREFLIGHT_OK bound to the hash of INPUT-SHA256SUMS; submit.sh refuses without it.
# usage: preflight-login.sh RUN_DIR
set -euo pipefail
R=$(cd -- "${1:?RUN_DIR}" && pwd -P); IN=$R/inputs
(cd "$IN" && sha256sum -c --quiet INPUT-SHA256SUMS)
# shellcheck disable=SC1091
. "$IN/pins.env"
fail() { echo "PREFLIGHT FAIL: $*"; exit 1; }
echo "== host $(hostname) $(uname -r) $(date -Is)"
test "$(git -C "$R/src" rev-parse HEAD)" = "$EXPECTED_COMMIT" || fail 'src HEAD'
test -z "$(git -C "$R/src" status --porcelain --ignored)" || fail 'src not clean'
test -x "$SINGULARITY" || fail "no $SINGULARITY"
test -r "$SIF" || fail 'image missing'
printf '%s  %s\n' "$RUNTIME_SHA" "$TB" | sha256sum -c --quiet - || fail 'runtime tarball hash'
gzip -t "$TB" || fail 'runtime tarball gzip CRC'
n=$(tar -tzf "$TB" | grep -c -E "^$TOOLDIR/bin/(lake|lean|leanchecker)\$" || true)
[ "$n" = 3 ] || fail "runtime archive lacks lake/lean/leanchecker ($n of 3)"
P=$(mktemp -d "/tmp/stratham-d8-pre.XXXXXX"); trap 'chmod -R u+w "$P" 2>/dev/null; rm -rf -- "$P"' EXIT
mkdir -p "$P/tc" "$P/cache"; tar -xzf "$TB" -C "$P/tc"
TOOLBIN="$P/tc/$TOOLDIR/bin"
"$SINGULARITY" exec --cleanenv --bind /tmp:/tmp --pwd "$R/src" \
  --env "PATH=$TOOLBIN:/usr/bin:/bin,XDG_CACHE_HOME=$P/cache,LC_ALL=C,LEAN_NUM_THREADS=3,LAKE_ARTIFACT_CACHE=false,GIT_TERMINAL_PROMPT=0,GIT_CONFIG_NOSYSTEM=1,GIT_CONFIG_GLOBAL=/dev/null" \
  "$SIF" bash -c 'for c in git lake lean leanchecker python3 timeout curl tar gzip sha256sum awk; do type -P "$c" || echo "MISSING $c"; done; lean --version; lake --version; python3 -I -c "import resource, subprocess; print(\"PY_OK\")"' \
  | tee "$R/preflight-container.log"
grep -q MISSING "$R/preflight-container.log" && fail 'a tool is missing inside the image'
grep -q 'version 4.35.0' "$R/preflight-container.log" || fail 'not Lean 4.35.0'
grep -q PY_OK "$R/preflight-container.log" || fail 'python3 resource module unusable in the image'
for c in sha256sum tar gzip awk mktemp tee df sacct sbatch; do type -P "$c" >/dev/null || fail "host lacks $c"; done
avail=$(df -P --block-size=1G "$R" | awk 'NR==2{print $4}'); [ "$avail" -ge 20 ] || fail "scratch has ${avail}G free"
used=$(squeue -u "$USER" -h -t R,PD -q resourcecap_plus -o '%C' | awk '{s+=$1} END{print s+0}')
echo "QOS resourcecap_plus: ${used} CPUs in use/pending; this pilot needs 4"
[ $((used + 4)) -le 1440 ] || fail 'QOS CPU cap'
sha256sum "$IN/INPUT-SHA256SUMS" | awk '{print $1}' > "$R/PREFLIGHT_OK"
echo "PREFLIGHT_OK $(cat "$R/PREFLIGHT_OK")"
