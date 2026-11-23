#!/usr/bin/env bash
#SBATCH --job-name=stratham-l11-lchk
#SBATCH --partition=nova_20
#SBATCH --qos=resourcecap_plus
#SBATCH --nodes=1
#SBATCH --ntasks=1
#SBATCH --time=1-00:00:00
#SBATCH --no-requeue
# --cpus-per-task, --mem, --array and --dependency come from submit.sh.
# L11 array task. Task 0: default-mode leanchecker of every manifest target, serial (wave L6: 794 s for 73).
# Task i >= 1: `lake env leanchecker --fresh <line i of targets-fresh.txt>`, one process (wave L6: 43-44 min,
# 7.6-7.7 GB peak RSS, 0.98 core: user CPU 2570 s of 2617 s wall). Packing: node-wide fs.file-max is 262144
# and one --fresh run holds about 62k open files (L6 peak 123,800 for two), so at most three tasks may
# share a 128 GB nova_20 node; submit.sh enforces that through --mem (36G -> 3 per node).
# Unchanged replay.py (sha256 10e90176..., the same file as in waves L5-L7). Verification only.
# usage (via submit.sh): sbatch --array=... task.sbatch RUN_DIR
set -euo pipefail
R=$(cd -- "${1:?RUN_DIR}" && pwd -P); IN=$R/inputs; SH=$R/shared
: "${SLURM_JOB_ID:?}" "${SLURM_ARRAY_JOB_ID:?needs an array}" "${SLURM_ARRAY_TASK_ID:?}"
(cd "$IN" && sha256sum -c --quiet INPUT-SHA256SUMS)
# shellcheck disable=SC1091
. "$IN/pins.env"
I=$SLURM_ARRAY_TASK_ID
bval() { grep -m1 "^$1=" "$SH/BUILD_OK" | cut -d= -f2-; }
test -s "$SH/BUILD_OK"
[ "$(bval commit)" = "$EXPECTED_COMMIT" ] && [ "$(bval tree)" = "$EXPECTED_TREE" ]
[ "$(bval inputs_sha256)" = "$(sha256sum "$IN/INPUT-SHA256SUMS" | awk '{print $1}')" ]
if [ "$I" = 0 ]; then MODE=default; TARGET=ALL; TMO=3600
else
  MODE=fresh; TMO=14400
  TARGET=$(sed -n "${I}p" "$IN/targets-fresh.txt"); [ -n "$TARGET" ] || { echo "no target line $I"; exit 64; }
fi
OUT=$R/tasks/$(printf '%03d' "$I")-$SLURM_JOB_ID
mkdir -- "$OUT"
exec > >(tee -a "$OUT/task.log") 2>&1
START=$(date -Is)
echo "node=$(hostname) job=$SLURM_JOB_ID array=${SLURM_ARRAY_JOB_ID}_$I mode=$MODE target=$TARGET start=$START"
G=; monitor_pid=
cleanup() {
  rc=$?; trap - EXIT
  if [ -n "$monitor_pid" ]; then kill "$monitor_pid" 2>/dev/null || true; wait "$monitor_pid" 2>/dev/null || true; fi
  {
    echo "index=$I"; echo "mode=$MODE"; echo "target=$TARGET"; echo "rc=$rc"
    echo "commit=$EXPECTED_COMMIT"; echo "tree=$EXPECTED_TREE"
    echo "inputs_sha256=$(bval inputs_sha256)"; echo "ws_tar_sha256=${WS_SEEN:-NA}"
    echo "leanchecker_sha256=${LC_SEEN:-NA}"; echo "node=$(hostname)"; echo "job=$SLURM_JOB_ID"
    echo "array_job=$SLURM_ARRAY_JOB_ID"; echo "start=$START"; echo "end=$(date -Is)"
  } > "$OUT/task.result"
  echo "PROCESS_EXIT=$rc end=$(date -Is)"
  if [ -n "$G" ]; then chmod -R u+w "$G" 2>/dev/null || true; rm -rf -- "$G" 2>/dev/null || true; fi
  exit "$rc"
}
trap cleanup EXIT
for name in GIT_DIR GIT_WORK_TREE GIT_INDEX_FILE GIT_COMMON_DIR GIT_OBJECT_DIRECTORY GIT_ALTERNATE_OBJECT_DIRECTORIES; do unset "$name"; done
# Spread the staging reads (image 2.7 GB, runtime 0.96 GB, workspace tarball) over about 5 minutes.
sleep $(( (I * 11) % 301 ))
avail=$(df -P --block-size=1G /tmp | awk 'NR==2{print $4}'); echo "tmp_avail_G=$avail"
[ "$avail" -ge 30 ] || { echo 'NODE /tmp TOO SMALL'; exit 76; }
G=$(mktemp -d "/tmp/stratham-l11t-${SLURM_JOB_ID}.XXXXXX")
mkdir -p "$G/cache" "$G/tc" "$G/pkg"
cp -- "$IN/replay.py" "$IN/modules-all.txt" "$G/pkg/"
printf '%s  %s\n' "$RUNTIME_SHA" "$TB" | sha256sum -c --quiet -
cp -- "$SIF" "$G/image.sif"
tar -xzf "$TB" -C "$G/tc"
readonly TOOLBIN="$G/tc/$TOOLDIR/bin"
WS_SEEN=$(sha256sum "$SH/ws.tar.gz" | awk '{print $1}')
[ "$WS_SEEN" = "$(bval ws_tar_sha256)" ] || { echo "WORKSPACE TARBALL HASH MISMATCH $WS_SEEN"; exit 77; }
tar -xzf "$SH/ws.tar.gz" -C "$G"
find "$G/tc" "$G/ws" -xdev -exec touch -a -h {} +   # Easley's 10-day /tmp cleaner reads atime (skill, 2026-10-20)
LC_SEEN=$(sha256sum "$TOOLBIN/leanchecker" | awk '{print $1}')
[ "$LC_SEEN" = "$(bval leanchecker_sha256)" ] || { echo 'CHECKER BINARY DIFFERS FROM THE BUILD JOB'; exit 78; }
[ "$(sha256sum "$TOOLBIN/lean" | awk '{print $1}')" = "$(bval lean_sha256)" ]
run() {
  "$SINGULARITY" exec --cleanenv --bind /tmp:/tmp --bind "$OUT:$OUT" --pwd "$G/ws" \
    --env "PATH=$TOOLBIN:/usr/bin:/bin,XDG_CACHE_HOME=$G/cache,LC_ALL=C,LEAN_NUM_THREADS=3,LAKE_ARTIFACT_CACHE=false,GIT_TERMINAL_PROMPT=0,GIT_CONFIG_NOSYSTEM=1,GIT_CONFIG_GLOBAL=/dev/null" \
    "$G/image.sif" bash -eu -o pipefail -c "$1"
}
run "test \"\$(git rev-parse HEAD)\" = '$EXPECTED_COMMIT'; test \"\$(git rev-parse 'HEAD^{tree}')\" = '$EXPECTED_TREE'; test -z \"\$(git status --porcelain)\"; test \"\$(git -C .lake/packages/mathlib rev-parse HEAD)\" = '$MATHLIB_REV'; echo VERIFIED_COMMIT=$EXPECTED_COMMIT TREE=$EXPECTED_TREE MATHLIB=$MATHLIB_REV"
if [ "$MODE" = fresh ]; then
  printf '%s\n' "$TARGET" > "$G/pkg/modules-task.txt"
else
  cp -- "$G/pkg/modules-all.txt" "$G/pkg/modules-task.txt"
fi
run "for m in \$(cat '$G/pkg/modules-task.txt'); do test -s .lake/build/lib/lean/\$(echo \$m | tr . /).olean || { echo MISSING_OLEAN \$m; exit 1; }; done; echo OLEANS_PRESENT=\$(wc -l < '$G/pkg/modules-task.txt')"
# Open-file guard: start only while the node has room for one more --fresh run (about 62k files).
waited=0
while :; do
  NR=$(awk '{print $1}' /proc/sys/fs/file-nr)
  [ "$NR" -le "$FILE_NR_MAX" ] && break
  [ "$waited" -ge 7200 ] && { echo "FILE_NR_BUSY file-nr=$NR > $FILE_NR_MAX for 2 h; stopping"; exit 75; }
  echo "WAIT file-nr=$NR > $FILE_NR_MAX"; sleep 60; waited=$((waited + 60))
done
echo "PRE_REPLAY file-nr=$NR waited_s=$waited"
CG=/sys/fs/cgroup/memory/slurm/uid_$(id -u)/job_${SLURM_JOB_ID}
(while true; do
   printf '%s filenr=%s mem_usage=%s mem_max=%s\n' "$(date +%H:%M:%S)" "$(tr '\t' ' ' < /proc/sys/fs/file-nr)" \
     "$(cat "$CG/memory.usage_in_bytes" 2>/dev/null || echo NA)" "$(cat "$CG/memory.max_usage_in_bytes" 2>/dev/null || echo NA)"
   sleep 30; done) > "$OUT/monitor.log" & monitor_pid=$!
echo "REPLAY_STARTED $(date -Is)"   # submit.sh's pilot gate waits for this line
T0=$(date +%s)
set +e
run "python3 -I '$G/pkg/replay.py' $MODE '$G/pkg/modules-task.txt' '$OUT/$MODE' 1 $TMO"
rc_replay=$?
set -e
echo "PHASE replay_${MODE}_s=$(( $(date +%s) - T0 )) rc=$rc_replay"
run "test \"\$(git rev-parse 'HEAD^{tree}')\" = '$EXPECTED_TREE'; test -z \"\$(git status --porcelain)\"; echo SOURCE_UNCHANGED_AFTER_REPLAY"
[ "$rc_replay" = 0 ] || { echo "LEANCHECKER FAILED mode=$MODE target=$TARGET"; exit 7; }
echo "TASK_PASS mode=$MODE target=$TARGET"
