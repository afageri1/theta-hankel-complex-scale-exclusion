#!/usr/bin/env bash
set -euo pipefail

file="HodgeProofHP/Stage2MultiplicationOperatorSpec.lean"
expected="$(printf '%s\n' \
  '  exact MeasureTheory.MemLp.coeFn_toLp' \
  '    (hpCoordinateMulRepresentative (f : HPSpace)) hf')"
actual="$(sed -n '32,33p' "$file" | tr -d '\r')"

if [[ "$actual" != "$expected" ]]; then
  echo "STOP: lines 32–33 differ from the expected text; no change made."
  exit 1
fi

sed -i '32,33c\  exact MeasureTheory.MemLp.coeFn_toLp hf' "$file"

lake env lean "$file"
lake build HodgeProofHP.Stage2MultiplicationOperatorSpec
