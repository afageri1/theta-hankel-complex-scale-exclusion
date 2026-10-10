#!/usr/bin/env bash
set -euo pipefail

file="HodgeProofHP/Stage3SchrodingerApiAudit.lean"
source=".lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Deriv.lean"

if [[ ! -f "$source" ]]; then
  echo "STOP: SchwartzSpace/Deriv.lean is absent in this mathlib checkout."
  exit 1
fi

if [[ "$(sed -n '2p' "$file" | tr -d '\r')" != \
  "import Mathlib.Analysis.Distribution.SchwartzSpace" ]]; then
  echo "STOP: import line differs; no change made."
  exit 1
fi

sed -i \
  '2s#^import Mathlib.Analysis.Distribution.SchwartzSpace$#import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv#' \
  "$file"

lake build HodgeProofHP.Stage3SchrodingerApiAudit
lake env lean "$file"
