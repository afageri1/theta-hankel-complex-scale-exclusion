#!/usr/bin/env bash
set -euo pipefail

file="HodgeProofHP/Stage2MultiplicationDomainSubmodule.lean"
expected="  simp [hpCoordinateMulRepresentative, hx]"
actual="$(sed -n '15p' "$file" | tr -d '\r')"

if [[ "$actual" != "$expected" ]]; then
  echo "STOP: line 15 differs from the expected text; no change made."
  exit 1
fi

sed -i '15s/simp \[hpCoordinateMulRepresentative, hx\]/simp [hpCoordinateMulRepresentative]/' "$file"

lake env lean "$file"
lake build HodgeProofHP.Stage2MultiplicationDomainSubmodule
