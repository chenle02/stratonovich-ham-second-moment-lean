#!/usr/bin/env bash
#SBATCH --job-name=stratham-l6-lchk
#SBATCH --partition=nova_20
#SBATCH --qos=resourcecap_plus
#SBATCH --nodes=1
#SBATCH --ntasks=1
# cpus/mem/time are given on the sbatch command line (pilot vs all).
# Stratonovich-HAM second-moment Lean companion at bfa2fd0: fresh clone, lake exe cache get,
# fresh lake build of StratonovichHAMSecondMoment + StratonovichHAMSecondMoment.Axioms,
# then per-module leanchecker (default mode for all 35, and --fresh one module per invocation).
# Verification only; no Lean iteration on the cluster.
set -euo pipefail
if [ "$#" -ne 4 ]; then echo 'usage: gate.sbatch INPUT_DIR NEW_RESULT_DIR MODE(modules-MODE.txt) PARALLEL' >&2; exit 64; fi
IN=$(cd -- "$1" && pwd -P); RESULT=$2; MODE=$3; PAR=$4
[[ "$RESULT" = /* ]]; [[ "$MODE" =~ ^[a-z0-9]+$ ]]; [[ "$PAR" =~ ^[0-9]+$ ]]
: "${SLURM_JOB_ID:?needs a Slurm allocation}"
readonly EXPECTED_COMMIT=bfa2fd0ed721aa7bd2fc027a15b787d5024f4d57
readonly EXPECTED_TREE=8bd4a1e93a5fa13d3c0fac340cea9c7872f48ffc
readonly MATHLIB_REV=56a005855ea17e0b0958f73ec801ae140b0a1679
readonly RUNTIME_SHA=9bca7d29b89503da3ce0e015000ff7aa425788b93814adf3e34e5a4792fee18f
readonly SIF=<container>.sif
readonly TB=/scratch/<user>/<runtime-dir>/lean-4.35.0-runtime.tar.gz
readonly SINGULARITY=/tools/singularity-3.8.4/bin/singularity
mkdir -- "$RESULT"
exec > >(tee -a "$RESULT/gate.log") 2>&1
G=$(mktemp -d "/tmp/stratham-lchk-${SLURM_JOB_ID}.XXXXXX")
monitor_pid=
cleanup() {
  rc=$?
  trap - EXIT
  if [ -n "$monitor_pid" ]; then kill "$monitor_pid" 2>/dev/null || true; wait "$monitor_pid" 2>/dev/null || true; fi
  echo "PROCESS_EXIT=$rc end=$(date -Is)"
  chmod -R u+w "$G" 2>/dev/null || true
  rm -rf -- "$G" 2>/dev/null || true
  exit "$rc"
}
trap cleanup EXIT
for name in GIT_DIR GIT_WORK_TREE GIT_INDEX_FILE GIT_COMMON_DIR GIT_OBJECT_DIRECTORY GIT_ALTERNATE_OBJECT_DIRECTORIES; do unset "$name"; done
mkdir -p "$G/cache" "$G/tc" "$G/pkg"
echo "node=$(hostname) job=$SLURM_JOB_ID mode=$MODE par=$PAR cpus=${SLURM_CPUS_PER_TASK:-NA} start=$(date -Is) commit=$EXPECTED_COMMIT tree=$EXPECTED_TREE"
(cd "$IN" && sha256sum -c INPUT-SHA256SUMS)
cp -- "$IN/replay.py" "$IN"/modules-*.txt "$G/pkg/"; test -s "$G/pkg/modules-$MODE.txt"
printf '%s  %s\n' "$RUNTIME_SHA" "$TB" | sha256sum -c -
cp -- "$SIF" "$G/image.sif"
tar -xzf "$TB" -C "$G/tc"
readonly TOOLBIN="$G/tc/leanprover--lean4---v4.35.0/bin"
for tool in lake lean leanchecker; do test -x "$TOOLBIN/$tool"; done
# Fresh copy of the login-node clone (contains .git, no .lake).
cp -a -- "$IN/src" "$G/ws"
test ! -e "$G/ws/.lake"
run() {
  "$SINGULARITY" exec --cleanenv --bind /tmp:/tmp --bind "$RESULT:$RESULT" --pwd "$G/ws" \
    --env "PATH=$TOOLBIN:/usr/bin:/bin,XDG_CACHE_HOME=$G/cache,HOME=$G/cache,LC_ALL=C,LEAN_NUM_THREADS=3,LAKE_ARTIFACT_CACHE=false,GIT_TERMINAL_PROMPT=0,GIT_CONFIG_NOSYSTEM=1,GIT_CONFIG_GLOBAL=/dev/null" \
    "$G/image.sif" bash -eu -o pipefail -c "$1"
}
CG=/sys/fs/cgroup/memory/slurm/uid_$(id -u)/job_${SLURM_JOB_ID}
(while true; do
   printf '%s filenr=%s mem_usage=%s mem_max=%s\n' "$(date +%H:%M:%S)" "$(tr '\t' ' ' < /proc/sys/fs/file-nr)" \
     "$(cat "$CG/memory.usage_in_bytes" 2>/dev/null || echo NA)" "$(cat "$CG/memory.max_usage_in_bytes" 2>/dev/null || echo NA)"
   sleep 10; done) > "$RESULT/monitor.log" & monitor_pid=$!
run "test \"\$(git rev-parse HEAD)\" = '$EXPECTED_COMMIT'; test \"\$(git rev-parse 'HEAD^{tree}')\" = '$EXPECTED_TREE'; test -z \"\$(git status --porcelain --ignored)\"; echo VERIFIED_COMMIT=$EXPECTED_COMMIT TREE=$EXPECTED_TREE CLEAN_NO_IGNORED"
# Manifest = source files + umbrella; umbrella imports = all modules except Axioms and itself.
run "{ find StratonovichHAMAudit StratonovichHAMSecondMoment -name '*.lean' | sed 's/\\.lean\$//; s#/#.#g' | LC_ALL=C sort; echo StratonovichHAMSecondMoment; } | diff - '$G/pkg/modules-all.txt'; grep -E '^import StratonovichHAM' StratonovichHAMSecondMoment.lean | awk '{print \$2}' | LC_ALL=C sort > '$G/umb.txt'; grep -v -x -e StratonovichHAMSecondMoment -e StratonovichHAMSecondMoment.Axioms '$G/pkg/modules-all.txt' | diff - '$G/umb.txt'; echo MANIFEST_OK modules=\$(wc -l < '$G/pkg/modules-all.txt')"
run 'cat lean-toolchain; lean --version; lake --version; for c in git lake lean leanchecker python3 timeout curl; do type -P "$c" || echo "MISSING $c"; done' | tee "$RESULT/runtime-preflight.log"
grep -q 'version 4.35.0' "$RESULT/runtime-preflight.log"
if grep -q MISSING "$RESULT/runtime-preflight.log"; then echo 'PREFLIGHT MISSING TOOL'; exit 3; fi
run "sha256sum '$TOOLBIN/lean' '$TOOLBIN/lake' '$TOOLBIN/leanchecker'" | tee "$RESULT/runtime-binaries.sha256"
echo "ulimit_n=$(ulimit -n) file_max=$(cat /proc/sys/fs/file-max)"
T0=$(date +%s)
cache_ready=0
for attempt in 1 2; do
  set +e
  run 'timeout -k 30s 1800s lake exe cache get' > "$RESULT/cache-get-$attempt.log" 2>&1
  cache_rc=$?
  set -e
  tail -4 "$RESULT/cache-get-$attempt.log"
  echo "CACHE attempt=$attempt rc=$cache_rc"
  if [ "$cache_rc" -eq 0 ]; then cache_ready=1; break; fi
done
[ "$cache_ready" = 1 ] || { echo 'CACHE GET FAILED twice; stopping'; exit 4; }
T1=$(date +%s); echo "PHASE cache_get_s=$((T1-T0))"
run "test \"\$(git -C .lake/packages/mathlib rev-parse HEAD)\" = '$MATHLIB_REV'; echo MATHLIB_PIN_OK=$MATHLIB_REV"
# No project olean may exist before the fresh build.
test ! -e "$G/ws/.lake/build/lib/lean/StratonovichHAMSecondMoment.olean"; test ! -e "$G/ws/.lake/build/lib/lean/StratonovichHAMAudit"; echo NO_PROJECT_OLEANS_BEFORE_BUILD
run 'timeout -k 60s 7200s lake build StratonovichHAMSecondMoment StratonovichHAMSecondMoment.Axioms' > "$RESULT/build.log" 2>&1 || { tail -40 "$RESULT/build.log"; echo 'BUILD FAILED'; exit 5; }
tail -3 "$RESULT/build.log"
T2=$(date +%s); echo "PHASE build_s=$((T2-T1))"; echo 'FRESH_BUILD=PASS'
run "for m in \$(cat '$G/pkg/modules-all.txt'); do f=.lake/build/lib/lean/\$(echo \$m | tr . /).olean; test -s \$f || { echo MISSING_OLEAN \$m; exit 1; }; done; echo ALL_OLEANS_PRESENT=$(wc -l < "$G/pkg/modules-all.txt")"
# Default-mode replay (same mode as verification/leanchecker-2026-11-10), serial.
set +e
run "python3 -I '$G/pkg/replay.py' default '$G/pkg/modules-all.txt' '$RESULT/default' 1 3600"
rc_default=$?
set -e
T3=$(date +%s); echo "PHASE replay_default_s=$((T3-T2)) rc=$rc_default"
# --fresh replay: one module per invocation, PAR at a time. If another job on this node already
# holds many open files (node-wide fs.file-max 262144; one heavy --fresh run holds ~62-72k), run serially.
NR0=$(awk '{print $1}' /proc/sys/fs/file-nr)
echo "PRE_FRESH file-nr=$NR0 requested_par=$PAR"
if [ "$NR0" -gt 60000 ] && [ "$PAR" -gt 1 ]; then PAR=1; echo "PAR_REDUCED_TO_1 because file-nr=$NR0 > 60000 before the fresh phase"; fi
set +e
run "python3 -I '$G/pkg/replay.py' fresh '$G/pkg/modules-$MODE.txt' '$RESULT/fresh' $PAR 14400"
rc_fresh=$?
set -e
T4=$(date +%s); echo "PHASE replay_fresh_s=$((T4-T3)) rc=$rc_fresh"
run "test \"\$(git rev-parse 'HEAD^{tree}')\" = '$EXPECTED_TREE'; test -z \"\$(git status --porcelain)\"; echo SOURCE_UNCHANGED_AFTER_GATE"
[ "$rc_default" = 0 ] && [ "$rc_fresh" = 0 ] || { echo 'LEANCHECKER: at least one module FAILED'; exit 7; }
echo "GATE_PROCESS_PASS mode=$MODE: fresh build + default replay ($(wc -l < "$G/pkg/modules-all.txt")) + --fresh replay ($(wc -l < "$G/pkg/modules-$MODE.txt")); terminal Slurm accounting still required"
