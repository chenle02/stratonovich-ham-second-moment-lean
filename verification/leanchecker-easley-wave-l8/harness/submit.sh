#!/usr/bin/env bash
# EASLEY LOGIN NODE. Submit the L11 campaign in stages. Run only with Le's go-ahead for the wave's Easley gate.
#
# usage: submit.sh RUN_DIR pilot              build job + array task 1 (first --fresh target) after it
#        submit.sh RUN_DIR rest  [THROTTLE]   after the pilot task printed REPLAY_STARTED: task 0 + tasks 2..N
#        submit.sh RUN_DIR redo  LIST         resubmit array indices (e.g. 5,17-18) listed by collect.py
# env: CPUS (default 2: measured 0.98 core per --fresh run), MEM (default 36G: caps packing at 3 per node
#      for the node-wide open-file limit; measured peak 7.7 GB), THROTTLE default 100 (whole campaign at once).
set -euo pipefail
R=$(cd -- "${1:?RUN_DIR}" && pwd -P); STAGE=${2:?pilot|rest|redo}; IN=$R/inputs
CPUS=${CPUS:-2}; MEM=${MEM:-36G}
(cd "$IN" && sha256sum -c --quiet INPUT-SHA256SUMS)
[ -s "$R/PREFLIGHT_OK" ] && [ "$(cat "$R/PREFLIGHT_OK")" = "$(sha256sum "$IN/INPUT-SHA256SUMS" | awk '{print $1}')" ] \
  || { echo 'no PREFLIGHT_OK for these inputs: run preflight-login.sh first'; exit 2; }
[ -f "$R/STOP" ] && { echo "STOP file present (two identical failure signatures): $(cat "$R/STOP")"; exit 3; }
N=$(wc -l < "$IN/targets-fresh.txt")
J=$R/jobs.txt; touch "$J"
OUTSPEC="$R/slurm-out/%x-%A_%a.out"
case "$STAGE" in
  pilot)
    grep -q '^build ' "$J" && { echo 'build already submitted'; exit 4; }
    B=$(sbatch --parsable --output="$R/slurm-out/%x-%j.out" "$IN/build.sbatch" "$R" < /dev/null)
    echo "build $B $(date -Is)" >> "$J"
    A=$(sbatch --parsable --dependency=afterok:"$B" --kill-on-invalid-dep=yes --array=1 \
          --cpus-per-task="$CPUS" --mem="$MEM" --output="$OUTSPEC" "$IN/task.sbatch" "$R" < /dev/null)
    echo "pilot $A index=1 cpus=$CPUS mem=$MEM $(date -Is)" >> "$J"
    echo "SUBMITTED build=$B pilot_array=$A (task 1 = $(sed -n 1p "$IN/targets-fresh.txt"))" ;;
  rest)
    THR=${3:-100}
    B=$(awk '$1=="build"{print $2}' "$J"); [ -n "$B" ] || { echo 'no build job'; exit 4; }
    grep -q '^rest ' "$J" && { echo 'rest already submitted'; exit 4; }
    P=$(ls "$R"/tasks/001-*/task.log 2>/dev/null | head -1)
    [ -n "$P" ] && grep -q '^REPLAY_STARTED' "$P" || { echo 'pilot task has not reached REPLAY_STARTED; wait'; exit 5; }
    grep -q -E 'FAIL|MISMATCH|TOO SMALL|FILE_NR_BUSY' "$P" && { echo "pilot log shows a failure: $P"; exit 6; }
    st=$(sacct -n -X -j "$B" -o State -P | head -1)
    [ "$st" = COMPLETED ] || { echo "build job $B state=$st (need COMPLETED)"; exit 7; }
    [ -s "$R/shared/BUILD_OK" ] || { echo 'no BUILD_OK'; exit 7; }
    LIST="0"; [ "$N" -ge 2 ] && LIST="0,2-$N"
    # The build already COMPLETED 0:0 and BUILD_OK is sealed; each task re-checks BUILD_OK and the tarball hash,
    # so no --dependency is needed (an afterok on a purged job id would be rejected).
    A=$(sbatch --parsable --array="$LIST%$THR" --cpus-per-task="$CPUS" --mem="$MEM" \
          --output="$OUTSPEC" "$IN/task.sbatch" "$R" < /dev/null)
    echo "rest $A indices=$LIST throttle=$THR cpus=$CPUS mem=$MEM $(date -Is)" >> "$J"
    echo "SUBMITTED rest_array=$A indices=$LIST" ;;
  redo)
    LIST=${3:?index list from collect.py}
    A=$(sbatch --parsable --array="$LIST" --cpus-per-task="$CPUS" --mem="$MEM" \
          --output="$OUTSPEC" "$IN/task.sbatch" "$R" < /dev/null)
    echo "redo $A indices=$LIST cpus=$CPUS mem=$MEM $(date -Is)" >> "$J"
    echo "SUBMITTED redo_array=$A indices=$LIST" ;;
  *) echo "unknown stage $STAGE"; exit 64 ;;
esac
