#!/usr/bin/env bash
# EASLEY LOGIN NODE. Submit the single D8 pilot job. Run only with Le's go-ahead (L11 decision 5).
# usage: submit.sh RUN_DIR
set -euo pipefail
R=$(cd -- "${1:?RUN_DIR}" && pwd -P); IN=$R/inputs
(cd "$IN" && sha256sum -c --quiet INPUT-SHA256SUMS)
[ -s "$R/PREFLIGHT_OK" ] && [ "$(cat "$R/PREFLIGHT_OK")" = "$(sha256sum "$IN/INPUT-SHA256SUMS" | awk '{print $1}')" ] \
  || { echo 'no PREFLIGHT_OK for these inputs: run preflight-login.sh first'; exit 2; }
[ -e "$R/jobs.txt" ] && { echo "already submitted: $(cat "$R/jobs.txt")"; exit 4; }
J=$(sbatch --parsable --output="$R/slurm-out/%x-%j.out" "$IN/pilot.sbatch" "$R" < /dev/null)
echo "pilot $J $(date -Is)" > "$R/jobs.txt"
echo "SUBMITTED pilot=$J; afterwards: python3 -I $IN/collect.py $R"
