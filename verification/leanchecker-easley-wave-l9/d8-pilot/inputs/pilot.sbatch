#!/usr/bin/env bash
#SBATCH --job-name=stratham-d8-pilot
#SBATCH --partition=nova_20
#SBATCH --qos=resourcecap_plus
#SBATCH --nodes=1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=4
#SBATCH --mem=16G
#SBATCH --time=1-00:00:00
#SBATCH --no-requeue
# D8 Mathlib pilot (waves L12-L14, items K5/K6): ONE job, measurement only, no Lean iteration on Easley.
# Sizing from <MACHINE> (D8-FEASIBILITY.md section 2): probe elaboration 3-9 s wall, peak RSS 3.5-7.0 GB;
# leanchecker --fresh of one companion module 43-44 min, one core, 7.7 GB peak (waves L3/L6 on Easley).
# 4 CPUs = LEAN_NUM_THREADS=3 elaboration + the monitor; 16G = 1.8x the 8.75 GB --fresh peak (<MACHINE>, 30.7 min); walltime one day
# because Slurm cannot extend it (skill hpc-classification-walltime-at-least-one-day); expected ~1.3 h.
# Phases: cache get -> elaborate every probe (expected rc from expect.tsv) -> compile FRESH_PROBE to an olean
# -> leanchecker (default) and leanchecker --fresh on it. Results: RUN_DIR/pilot/results.tsv, PILOT_DONE.
# usage (via submit.sh): sbatch pilot.sbatch RUN_DIR
set -euo pipefail
R=$(cd -- "${1:?RUN_DIR}" && pwd -P); IN=$R/inputs; O=$R/pilot
: "${SLURM_JOB_ID:?needs a Slurm allocation}"
(cd "$IN" && sha256sum -c --quiet INPUT-SHA256SUMS)
# shellcheck disable=SC1091
. "$IN/pins.env"
mkdir -- "$O"   # write-once: a second pilot needs a new RUN_DIR
exec > >(tee -a "$O/pilot-job.log") 2>&1
G=$(mktemp -d "/tmp/stratham-d8-${SLURM_JOB_ID}.XXXXXX")
monitor_pid=
cleanup() {
  rc=$?; trap - EXIT
  if [ -n "$monitor_pid" ]; then kill "$monitor_pid" 2>/dev/null || true; wait "$monitor_pid" 2>/dev/null || true; fi
  echo "PROCESS_EXIT=$rc end=$(date -Is)"
  chmod -R u+w "$G" 2>/dev/null || true; rm -rf -- "$G" 2>/dev/null || true
  exit "$rc"
}
trap cleanup EXIT
for name in GIT_DIR GIT_WORK_TREE GIT_INDEX_FILE GIT_COMMON_DIR GIT_OBJECT_DIRECTORY GIT_ALTERNATE_OBJECT_DIRECTORIES; do unset "$name"; done
echo "node=$(hostname) job=$SLURM_JOB_ID cpus=${SLURM_CPUS_PER_TASK:-NA} start=$(date -Is) commit=$EXPECTED_COMMIT mathlib=$MATHLIB_REV"
avail=$(df -P --block-size=1G /tmp | awk 'NR==2{print $4}'); echo "tmp_avail_G=$avail"; [ "$avail" -ge 20 ] || { echo 'NODE /tmp TOO SMALL'; exit 76; }
mkdir -p "$G/cache" "$G/tc" "$G/olean/D8Probe"
printf '%s  %s\n' "$RUNTIME_SHA" "$TB" | sha256sum -c -
cp -- "$SIF" "$G/image.sif"
tar -xzf "$TB" -C "$G/tc"; find "$G/tc" -xdev -exec touch -a -h {} +
readonly TOOLBIN="$G/tc/$TOOLDIR/bin"
cp -a -- "$R/src" "$G/ws"; test ! -e "$G/ws/.lake"
cp -- "$IN/measure.py" "$G/measure.py"; cp -a -- "$IN/probes" "$G/probes"
run() {
  "$SINGULARITY" exec --cleanenv --bind /tmp:/tmp --bind "$O:$O" --pwd "$G/ws" \
    --env "PATH=$TOOLBIN:/usr/bin:/bin,XDG_CACHE_HOME=$G/cache,LC_ALL=C,LEAN_NUM_THREADS=${2:-3},LAKE_ARTIFACT_CACHE=false,GIT_TERMINAL_PROMPT=0,GIT_CONFIG_NOSYSTEM=1,GIT_CONFIG_GLOBAL=/dev/null" \
    "$G/image.sif" bash -eu -o pipefail -c "$1"
}
CG=/sys/fs/cgroup/memory/slurm/uid_$(id -u)/job_${SLURM_JOB_ID}
(while true; do
   fnr=$(tr '\t' ' ' < /proc/sys/fs/file-nr)
   printf '%s filenr=%s mem_usage=%s mem_max=%s\n' "$(date +%H:%M:%S)" "$fnr" \
     "$(cat "$CG/memory.usage_in_bytes" 2>/dev/null || echo NA)" "$(cat "$CG/memory.max_usage_in_bytes" 2>/dev/null || echo NA)"
   [ "${fnr%% *}" -le "$FILE_NR_MAX" ] || echo "FILE_NR_BUSY ${fnr%% *} > $FILE_NR_MAX"
   sleep 10; done) > "$O/monitor.log" & monitor_pid=$!
run "test \"\$(git rev-parse HEAD)\" = '$EXPECTED_COMMIT'; test \"\$(git rev-parse 'HEAD^{tree}')\" = '$EXPECTED_TREE'; echo VERIFIED_COMMIT"
run 'lean --version; for c in git lake lean leanchecker python3 timeout; do type -P "$c" || echo "MISSING $c"; done' | tee "$O/runtime-preflight.log"
if grep -q MISSING "$O/runtime-preflight.log"; then echo 'PREFLIGHT MISSING TOOL'; exit 3; fi
# Phase 1: Mathlib oleans only (no project build: probes import Mathlib alone)
T0=$(date +%s); ok=0
for attempt in 1 2 3; do
  set +e; run 'timeout -k 30s 1200s lake exe cache get' > "$O/cache-get-$attempt.log" 2>&1; crc=$?; set -e
  echo "CACHE attempt=$attempt rc=$crc"; [ "$crc" -eq 0 ] && { ok=1; break; }
done
[ "$ok" = 1 ] || { echo 'CACHE GET FAILED three times'; exit 4; }
run "test \"\$(git -C .lake/packages/mathlib rev-parse HEAD)\" = '$MATHLIB_REV'; echo MATHLIB_PIN_OK"
echo "PHASE cache_get_s=$(( $(date +%s) - T0 ))"
# Phase 2: elaborate each probe twice (cold page cache, then warm), LEAN_NUM_THREADS=3
RES=$O/results.tsv; : > "$RES"
for pass in cold warm; do
  while read -r p; do
    run "python3 -I '$G/measure.py' '$p.$pass' '$RES' -- timeout -k 30s 1800s lake env lean '$G/probes/$p.lean'" > "$O/elab-$p.$pass.log" 2>&1 || true
    tail -1 "$O/elab-$p.$pass.log"
  done < "$IN/probes.txt"
done
# Phase 3: the workload probe as a module, then leanchecker default and --fresh (the replay cost a D8 module adds)
F=$FRESH_PROBE
# Lean 4.35 derives the module name from --root (validated on <MACHINE>: olean 7.9 s, leanchecker default 7.3 s)
mkdir -p "$G/srcroot/D8Probe"; cp -- "$G/probes/$F.lean" "$G/srcroot/D8Probe/$F.lean"
run "python3 -I '$G/measure.py' 'olean.$F' '$RES' -- lake env lean --root='$G/srcroot' -o '$G/olean/D8Probe/$F.olean' '$G/srcroot/D8Probe/$F.lean'"
test -s "$G/olean/D8Probe/$F.olean"
run "python3 -I '$G/measure.py' 'check.$F' '$RES' -- lake env bash -c 'LEAN_PATH=$G/olean:\$LEAN_PATH exec timeout -k 60s 3600s leanchecker D8Probe.$F'" 1
run "python3 -I '$G/measure.py' 'fresh.$F' '$RES' -- lake env bash -c 'LEAN_PATH=$G/olean:\$LEAN_PATH exec timeout -k 60s 14400s leanchecker --fresh D8Probe.$F'" 1
# Judge: every probe rc equals its expectation in both passes; both checker runs rc 0
bad=0
while IFS=$'\t' read -r label rc _; do
  base=${label%.*}; kind=${label##*.}
  case "$label" in
    olean.*|check.*|fresh.*) want=0 ;;
    *) want=$(awk -F'\t' -v p="$base" '$1==p{print $2}' "$IN/expect.tsv") ;;
  esac
  [ "$rc" = "$want" ] || { echo "MISMATCH $label rc=$rc expected=$want ($kind)"; bad=1; }
done < "$RES"
grep -q FILE_NR_BUSY "$O/monitor.log" && echo 'NOTE: file-nr exceeded FILE_NR_MAX during the run (see monitor.log)'
{ echo "job=$SLURM_JOB_ID node=$(hostname) commit=$EXPECTED_COMMIT mathlib=$MATHLIB_REV"
  echo "inputs_sha256=$(sha256sum "$IN/INPUT-SHA256SUMS" | awk '{print $1}')"
  echo "results_sha256=$(sha256sum "$RES" | awk '{print $1}')"
  echo "mismatch=$bad finished=$(date -Is)"; } > "$O/PILOT_DONE"
chmod 444 "$O/PILOT_DONE" "$RES"
[ "$bad" = 0 ] && echo 'PILOT_PASS' || { echo 'PILOT_MISMATCH'; exit 8; }
