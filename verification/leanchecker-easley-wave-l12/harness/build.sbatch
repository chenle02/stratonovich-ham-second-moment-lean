#!/usr/bin/env bash
#SBATCH --job-name=stratham-l11-build
#SBATCH --partition=nova_20
#SBATCH --qos=resourcecap_plus
#SBATCH --nodes=1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=4
#SBATCH --mem=24G
#SBATCH --time=1-00:00:00
#SBATCH --no-requeue
# L11 shared build (one job). Fresh copy of the login-node clone at the pinned commit, lake exe cache get,
# fresh lake build of the umbrella and Axioms, then one gzip tarball of the whole workspace (.git, .lake
# with Mathlib oleans and project oleans) on scratch, with its sha256 and a BUILD_OK binding record.
# The array (task.sbatch) depends on this job with --dependency=afterok. Verification only: no Lean
# iteration on the cluster. Measured basis (wave L6 job 5692528, node831): cache get 88 s, build 319 s.
# usage (via submit.sh): sbatch build.sbatch RUN_DIR
set -euo pipefail
R=$(cd -- "${1:?RUN_DIR}" && pwd -P); IN=$R/inputs; SH=$R/shared
: "${SLURM_JOB_ID:?needs a Slurm allocation}"
(cd "$IN" && sha256sum -c --quiet INPUT-SHA256SUMS)
# shellcheck disable=SC1091
. "$IN/pins.env"
mkdir -- "$SH"   # a second build needs a new RUN_DIR: shared outputs are write-once
exec > >(tee -a "$SH/build-job.log") 2>&1
G=$(mktemp -d "/tmp/stratham-l11b-${SLURM_JOB_ID}.XXXXXX")
monitor_pid=
cleanup() {
  rc=$?; trap - EXIT
  if [ -n "$monitor_pid" ]; then kill "$monitor_pid" 2>/dev/null || true; wait "$monitor_pid" 2>/dev/null || true; fi
  echo "PROCESS_EXIT=$rc end=$(date -Is)"
  chmod -R u+w "$G" 2>/dev/null || true; rm -rf -- "$G" 2>/dev/null || true
  rm -f -- "$SH/ws.tar.gz.part"
  exit "$rc"
}
trap cleanup EXIT
for name in GIT_DIR GIT_WORK_TREE GIT_INDEX_FILE GIT_COMMON_DIR GIT_OBJECT_DIRECTORY GIT_ALTERNATE_OBJECT_DIRECTORIES; do unset "$name"; done
echo "node=$(hostname) job=$SLURM_JOB_ID cpus=${SLURM_CPUS_PER_TASK:-NA} start=$(date -Is) commit=$EXPECTED_COMMIT tree=$EXPECTED_TREE"
avail=$(df -P --block-size=1G /tmp | awk 'NR==2{print $4}'); echo "tmp_avail_G=$avail"; [ "$avail" -ge 40 ] || { echo 'NODE /tmp TOO SMALL'; exit 76; }
mkdir -p "$G/cache" "$G/tc" "$G/pkg"
cp -- "$IN/replay.py" "$IN/modules-all.txt" "$G/pkg/"
printf '%s  %s\n' "$RUNTIME_SHA" "$TB" | sha256sum -c -
cp -- "$SIF" "$G/image.sif"
tar -xzf "$TB" -C "$G/tc"; find "$G/tc" -xdev -exec touch -a -h {} +
readonly TOOLBIN="$G/tc/$TOOLDIR/bin"
for tool in lake lean leanchecker; do test -x "$TOOLBIN/$tool"; done
cp -a -- "$R/src" "$G/ws"; test ! -e "$G/ws/.lake"
run() {
  "$SINGULARITY" exec --cleanenv --bind /tmp:/tmp --bind "$SH:$SH" --pwd "$G/ws" \
    --env "PATH=$TOOLBIN:/usr/bin:/bin,XDG_CACHE_HOME=$G/cache,LC_ALL=C,LEAN_NUM_THREADS=3,LAKE_ARTIFACT_CACHE=false,GIT_TERMINAL_PROMPT=0,GIT_CONFIG_NOSYSTEM=1,GIT_CONFIG_GLOBAL=/dev/null" \
    "$G/image.sif" bash -eu -o pipefail -c "$1"
}
CG=/sys/fs/cgroup/memory/slurm/uid_$(id -u)/job_${SLURM_JOB_ID}
(while true; do
   printf '%s filenr=%s mem_usage=%s mem_max=%s\n' "$(date +%H:%M:%S)" "$(tr '\t' ' ' < /proc/sys/fs/file-nr)" \
     "$(cat "$CG/memory.usage_in_bytes" 2>/dev/null || echo NA)" "$(cat "$CG/memory.max_usage_in_bytes" 2>/dev/null || echo NA)"
   sleep 10; done) > "$SH/build-monitor.log" & monitor_pid=$!
run "test \"\$(git rev-parse HEAD)\" = '$EXPECTED_COMMIT'; test \"\$(git rev-parse 'HEAD^{tree}')\" = '$EXPECTED_TREE'; test -z \"\$(git status --porcelain --ignored)\"; echo VERIFIED_COMMIT=$EXPECTED_COMMIT TREE=$EXPECTED_TREE CLEAN_NO_IGNORED"
run "{ find StratonovichHAMAudit StratonovichHAMSecondMoment -name '*.lean' | sed 's/\\.lean\$//; s#/#.#g' | LC_ALL=C sort; echo StratonovichHAMSecondMoment; } | diff - '$G/pkg/modules-all.txt'; grep -E '^import StratonovichHAM' StratonovichHAMSecondMoment.lean | awk '{print \$2}' | LC_ALL=C sort > '$G/umb.txt'; grep -v -x -e StratonovichHAMSecondMoment -e StratonovichHAMSecondMoment.Axioms '$G/pkg/modules-all.txt' | diff - '$G/umb.txt'; echo MANIFEST_OK modules=\$(wc -l < '$G/pkg/modules-all.txt')"
run 'cat lean-toolchain; lean --version; lake --version; for c in git lake lean leanchecker python3 timeout curl; do type -P "$c" || echo "MISSING $c"; done' | tee "$SH/runtime-preflight.log"
grep -q 'version 4.35.0' "$SH/runtime-preflight.log"
if grep -q MISSING "$SH/runtime-preflight.log"; then echo 'PREFLIGHT MISSING TOOL'; exit 3; fi
run "sha256sum '$TOOLBIN/lean' '$TOOLBIN/lake' '$TOOLBIN/leanchecker'" | sed "s#$TOOLBIN/##" | tee "$SH/runtime-binaries.sha256"
echo "ulimit_n=$(ulimit -n) file_max=$(cat /proc/sys/fs/file-max)"
T0=$(date +%s)
cache_ready=0
for attempt in 1 2 3; do   # bounded: a cache get once hung for an hour (skill, 2026-10-26)
  set +e; run 'timeout -k 30s 1200s lake exe cache get' > "$SH/cache-get-$attempt.log" 2>&1; cache_rc=$?; set -e
  tail -4 "$SH/cache-get-$attempt.log"; echo "CACHE attempt=$attempt rc=$cache_rc"
  if [ "$cache_rc" -eq 0 ]; then cache_ready=1; break; fi
done
[ "$cache_ready" = 1 ] || { echo 'CACHE GET FAILED three times; stopping'; exit 4; }
T1=$(date +%s); echo "PHASE cache_get_s=$((T1-T0))"
run "test \"\$(git -C .lake/packages/mathlib rev-parse HEAD)\" = '$MATHLIB_REV'; echo MATHLIB_PIN_OK=$MATHLIB_REV"
test ! -e "$G/ws/.lake/build/lib/lean/StratonovichHAMSecondMoment.olean"; test ! -e "$G/ws/.lake/build/lib/lean/StratonovichHAMAudit"; echo NO_PROJECT_OLEANS_BEFORE_BUILD
run 'timeout -k 60s 7200s lake build StratonovichHAMSecondMoment StratonovichHAMSecondMoment.Axioms' > "$SH/build.log" 2>&1 || { tail -40 "$SH/build.log"; echo 'BUILD FAILED'; exit 5; }
tail -3 "$SH/build.log"
T2=$(date +%s); echo "PHASE build_s=$((T2-T1))"; echo 'FRESH_BUILD=PASS'
run "for m in \$(cat '$G/pkg/modules-all.txt'); do f=.lake/build/lib/lean/\$(echo \$m | tr . /).olean; test -s \$f || { echo MISSING_OLEAN \$m; exit 1; }; done; echo ALL_OLEANS_PRESENT=$(wc -l < "$G/pkg/modules-all.txt")"
run "test \"\$(git rev-parse 'HEAD^{tree}')\" = '$EXPECTED_TREE'; test -z \"\$(git status --porcelain)\"; echo SOURCE_UNCHANGED_AFTER_BUILD"
# One workspace tarball for every array task (GNU tar: atime = extraction time on the task node).
tar -C "$G" -cf - ws | gzip -1 > "$SH/ws.tar.gz.part"
gzip -t "$SH/ws.tar.gz.part"
WS_SHA=$(sha256sum "$SH/ws.tar.gz.part" | awk '{print $1}')
mv -- "$SH/ws.tar.gz.part" "$SH/ws.tar.gz"; chmod 444 "$SH/ws.tar.gz"
T3=$(date +%s); echo "PHASE tar_s=$((T3-T2)) ws_tar_bytes=$(stat -c %s "$SH/ws.tar.gz") ws_tar_sha256=$WS_SHA"
{
  echo "commit=$EXPECTED_COMMIT"; echo "tree=$EXPECTED_TREE"; echo "mathlib=$MATHLIB_REV"
  echo "inputs_sha256=$(sha256sum "$IN/INPUT-SHA256SUMS" | awk '{print $1}')"
  echo "manifest_sha256=$(sha256sum "$IN/modules-all.txt" | awk '{print $1}')"
  echo "targets_sha256=$(sha256sum "$IN/targets-fresh.txt" | awk '{print $1}')"
  echo "ws_tar_sha256=$WS_SHA"
  awk '{print $2"_sha256="$1}' "$SH/runtime-binaries.sha256"
  echo "build_job=$SLURM_JOB_ID"; echo "build_node=$(hostname)"; echo "built_at=$(date -Is)"
} > "$SH/BUILD_OK.tmp"
mv -- "$SH/BUILD_OK.tmp" "$SH/BUILD_OK"; chmod 444 "$SH/BUILD_OK"
cat "$SH/BUILD_OK"
echo "BUILD_JOB_PASS: fresh build of $(wc -l < "$G/pkg/modules-all.txt") targets; workspace tarball sealed"
