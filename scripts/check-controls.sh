#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2026 Le Chen
# SPDX-License-Identifier: Apache-2.0
#
# Check the negative controls and the per-module audit files.
#
# Each file under controls/ states a deliberately wrong variant of a checked
# fact (a wrong constant, sign, range or missing hypothesis). It is accepted as
# a control only when Lean rejects it for a mathematical reason:
#   * an unsolved goal `⊢ False`, or
#   * `decide` evaluating the stated proposition to false,
# and the log shows no unknown identifier, tactic, module or missing object
# file (those would mean the control broke, not that the mathematics refused).
# Each file under refutations/ proves that a wrong variant is false: it must
# compile, state a negation (¬) and contain no sorry. This is a stronger form
# of control (Lean proves the variant false instead of failing to prove it).
# Each file under Audit/ prints full types and axioms and must compile.
#
# Usage: scripts/check-controls.sh [LOGDIR]   (run after `lake build`)
set -uo pipefail
export LC_ALL=C.UTF-8
cd "$(dirname "$0")/.."
LOGDIR=${1:-$(mktemp -d)}
mkdir -p "$LOGDIR"
# Setup errors (matched case-insensitively; Lean 4.35 also tags errors, e.g.
# `error(lean.unknownIdentifier): Unknown identifier`): a control that hits one
# of these broke, it did not fail for a mathematical reason.
bad_setup='unknown (identifier|tactic|constant|namespace|option|attribute|declaration)|unknown module|invalid field|unexpected (end of input|token)|could not resolve|object file .* does not exist|maximum recursion|deterministic\) timeout|deterministic timeout'
fail=0; nctl=0; naud=0; nref=0
for f in controls/*/*.lean; do
  nctl=$((nctl + 1))
  log="$LOGDIR/$(echo "$f" | tr / _).log"
  lake env lean "$f" >"$log" 2>&1; rc=$?
  if [ "$rc" -eq 0 ]; then
    echo "FAIL control-accepted $f"; fail=1
  elif grep -Eiq "$bad_setup" "$log"; then
    echo "FAIL control-setup $f"; fail=1
  elif grep -q '⊢ False' "$log"; then
    echo "ok   control-false-goal $f"
  elif grep -q 'Tactic `decide` proved that the proposition' "$log" && grep -q 'is false' "$log"; then
    echo "ok   control-decide-false $f"
  else
    echo "FAIL control-unclassified $f"; fail=1
  fi
done
for f in refutations/*/*.lean; do
  [ -e "$f" ] || continue
  nref=$((nref + 1))
  log="$LOGDIR/$(echo "$f" | tr / _).log"
  if ! grep -q '¬' "$f"; then
    echo "FAIL refutation-no-negation $f"; fail=1
  elif grep -Eq '\b(sorry|admit)\b' "$f"; then
    echo "FAIL refutation-sorry $f"; fail=1
  elif lake env lean "$f" >"$log" 2>&1 && ! grep -q 'sorryAx\|declaration uses .sorry' "$log"; then
    echo "ok   refutation $f"
  else
    echo "FAIL refutation-does-not-compile $f"; fail=1
  fi
done
for f in Audit/*/*.lean; do
  naud=$((naud + 1))
  log="$LOGDIR/$(echo "$f" | tr / _).log"
  if lake env lean "$f" >"$log" 2>&1 && ! grep -q 'sorryAx' "$log"; then
    echo "ok   audit $f"
  else
    echo "FAIL audit $f"; fail=1
  fi
done
echo "controls: $nctl  refutations: $nref  audits: $naud  logs: $LOGDIR"
[ "$fail" -eq 0 ] && echo "check-controls: PASS" || echo "check-controls: FAIL"
exit "$fail"
