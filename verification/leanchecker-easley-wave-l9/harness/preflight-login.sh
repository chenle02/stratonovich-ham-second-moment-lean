#!/usr/bin/env bash
# EASLEY LOGIN NODE. Preflight before any sbatch (CLAUDE.md HPC rule 2; skill lean-easley-slurm-verification,
# "Before any sbatch"). Runs every command the jobs call, inside the job's image, with the job's binds,
# --cleanenv and the job's own PATH line, using `type -P` (never `command -v`). Writes RUN_DIR/PREFLIGHT_OK
# bound to the hash of INPUT-SHA256SUMS; submit.sh refuses without it.
# usage: preflight-login.sh RUN_DIR CPUS_PER_TASK
set -euo pipefail
R=$(cd -- "${1:?RUN_DIR}" && pwd -P); CPUS=${2:?CPUS_PER_TASK}; IN=$R/inputs
(cd "$IN" && sha256sum -c --quiet INPUT-SHA256SUMS)
# shellcheck disable=SC1091
. "$IN/pins.env"
fail() { echo "PREFLIGHT FAIL: $*"; exit 1; }
echo "== host $(hostname) $(uname -r) $(date -Is)"
# 1. staged clone
test "$(git -C "$R/src" rev-parse HEAD)" = "$EXPECTED_COMMIT" || fail 'src HEAD'
test "$(git -C "$R/src" rev-parse 'HEAD^{tree}')" = "$EXPECTED_TREE" || fail 'src tree'
test -z "$(git -C "$R/src" status --porcelain --ignored)" || fail 'src not clean'
( cd "$R/src" && { find StratonovichHAMAudit StratonovichHAMSecondMoment -name '*.lean' | sed 's/\.lean$//; s#/#.#g' | LC_ALL=C sort; echo StratonovichHAMSecondMoment; } ) \
  | diff - "$IN/modules-all.txt" || fail 'manifest differs from the staged source'
echo "MANIFEST_OK modules=$(wc -l < "$IN/modules-all.txt") fresh_targets=$(wc -l < "$IN/targets-fresh.txt")"
# 2. image, singularity, runtime archive
test -x "$SINGULARITY" || fail "no $SINGULARITY"
test -r "$SIF" || fail 'image missing'
printf '%s  %s\n' "$RUNTIME_SHA" "$TB" | sha256sum -c --quiet - || fail 'runtime tarball hash'
gzip -t "$TB" || fail 'runtime tarball gzip CRC'
n=$(tar -tzf "$TB" | grep -c -E "^$TOOLDIR/bin/(lake|lean|leanchecker)\$" || true)
[ "$n" = 3 ] || fail "runtime archive lacks lake/lean/leanchecker ($n of 3)"
# 3. the job's container environment, verbatim (runtime unpacked to a login-node temp dir only for this check)
P=$(mktemp -d "/tmp/stratham-l11-pre.XXXXXX"); trap 'chmod -R u+w "$P" 2>/dev/null; rm -rf -- "$P"' EXIT
mkdir -p "$P/tc" "$P/cache"; tar -xzf "$TB" -C "$P/tc"
TOOLBIN="$P/tc/$TOOLDIR/bin"
"$SINGULARITY" exec --cleanenv --bind /tmp:/tmp --pwd "$R/src" \
  --env "PATH=$TOOLBIN:/usr/bin:/bin,XDG_CACHE_HOME=$P/cache,LC_ALL=C,LEAN_NUM_THREADS=3,LAKE_ARTIFACT_CACHE=false,GIT_TERMINAL_PROMPT=0,GIT_CONFIG_NOSYSTEM=1,GIT_CONFIG_GLOBAL=/dev/null" \
  "$SIF" bash -c 'for c in git lake lean leanchecker python3 timeout curl tar gzip sha256sum; do type -P "$c" || echo "MISSING $c"; done; lean --version; lake --version' \
  | tee "$R/preflight-container.log"
grep -q MISSING "$R/preflight-container.log" && fail 'a tool is missing inside the image'
grep -q 'version 4.35.0' "$R/preflight-container.log" || fail 'not Lean 4.35.0'
# 4. host tools the job scripts call OUTSIDE the image (same OS image on nova_20 compute nodes; the pilot task re-checks)
for c in sha256sum tar gzip awk sed mktemp tee find touch df flock python3 sacct squeue sbatch; do type -P "$c" >/dev/null || fail "host lacks $c"; done
python3 -I -c 'import sys; assert sys.version_info >= (3, 7), sys.version' || fail 'login python3 too old for collect.py'
# 5. capacity: QOS headroom, partition idle CPUs, scratch quota
N=$(wc -l < "$IN/targets-fresh.txt")
need=$(( (N + 1) * CPUS + 4 ))
used=$(squeue -u "$USER" -h -t R,PD -q resourcecap_plus -o '%C' | awk '{s+=$1} END{print s+0}')
echo "QOS resourcecap_plus: in use/pending ${used} CPUs, cap 1440 per user, this campaign needs ${need}"
[ $((used + need)) -le 1440 ] || fail 'QOS CPU cap would be exceeded: lower the throttle (submit.sh THROTTLE)'
idle=$(sinfo -p nova_20 -h -N -o '%C' | awk -F/ '{s+=$2} END{print s+0}')
echo "nova_20 idle CPUs now: $idle (pending jobs: $(squeue -p nova_20 -h -t PD | wc -l))"
checkquota 2>/dev/null | sed -n '/scratch/,+1p' || true
avail=$(df -P --block-size=1G "$R" | awk 'NR==2{print $4}'); [ "$avail" -ge 50 ] || fail "scratch filesystem has ${avail}G free"
# 6. sandbox facts (comparator judges cannot run here; recorded, not a failure)
{ uname -r; cat /sys/kernel/security/lsm 2>/dev/null || echo 'no lsm file'; type -P bwrap || echo 'no bwrap'
  unshare --user --map-root-user true 2>&1 && echo USERNS_OK || echo USERNS_FAIL; } > "$R/preflight-sandbox.log"
sha256sum "$IN/INPUT-SHA256SUMS" | awk '{print $1}' > "$R/PREFLIGHT_OK"
echo "PREFLIGHT_OK $(cat "$R/PREFLIGHT_OK") cpus_per_task=$CPUS"
