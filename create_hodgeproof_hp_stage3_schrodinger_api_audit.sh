#!/usr/bin/env bash
set -euo pipefail

file="HodgeProofHP/Stage3SchrodingerApiAudit.lean"

if [[ ! -f HodgeProofHP/Stage2MultiplicationOperatorSpec.lean ]]; then
  echo "STOP: run from the hodgeproof-hp repository root."
  exit 1
fi

if [[ -e "$file" ]]; then
  echo "STOP: $file already exists; no file was replaced."
  exit 1
fi

cat > "$file" <<'LEAN'
import HodgeProofHP.Stage2MultiplicationOperatorSpec
import Mathlib.Analysis.Distribution.SchwartzSpace

/-!
Stage 3 API audit: Schwartz functions, derivatives, and passage to L².
No Schrödinger operator or spectral assertion is defined here.
-/

namespace HodgeProofHP

#check HPSpace
#check SchwartzMap
#check SchwartzMap.memLp
#check SchwartzMap.toLp
#check SchwartzMap.toLpCLM
#check SchwartzMap.fderivCLM
#check SchwartzMap.smulRightCLM
#check SchwartzMap.bilinLeftCLM
#check LinearPMap

end HodgeProofHP
LEAN

lake env lean "$file"
lake build HodgeProofHP.Stage3SchrodingerApiAudit
