#!/usr/bin/env bash
set -euo pipefail

if [[ ! -f lakefile.lean && ! -f lakefile.toml ]]; then
  echo "STOP: run from the hodgeproof-hp project root."
  exit 1
fi

lake build HodgeProofHP.Stage4ThetaHankelSquareFiniteness

target="HodgeProofHP/Stage4HankelOperatorApiAudit.lean"

if [[ -f "$target" ]]; then
  backup="${target}.before_create_$(date +%Y%m%d_%H%M%S)_$$"
  cp -p "$target" "$backup"
  echo "BACKUP: $backup"
fi

cat > "$target" <<'LEAN'
import HodgeProofHP.Stage4ThetaHankelSquareFiniteness
import Mathlib.MeasureTheory.Function.L2Space

/-!
API audit for constructing the half-line Hankel operator.
-/

noncomputable section

namespace HodgeProofHP

open MeasureTheory
open scoped ENNReal

def hpThetaHalfLineMeasure : Measure ℝ :=
  volume.restrict (Set.Ioi (0 : ℝ))

abbrev HPThetaHalfLineSpace :=
  Lp ℂ 2 hpThetaHalfLineMeasure

example : CompleteSpace HPThetaHalfLineSpace := inferInstance
example : InnerProductSpace ℂ HPThetaHalfLineSpace := inferInstance

#check MemLp
#check MemLp.toLp
#check Lp.memLp
#check ContinuousLinearMap
#check hpThetaHankelKernel_norm_sq_integrable
#check hpThetaHankelKernel_hermitian

end HodgeProofHP
LEAN

lake env lean "$target"

mathlib_root=".lake/packages/mathlib/Mathlib"

if [[ ! -d "$mathlib_root" ]]; then
  echo "STOP: mathlib source directory not found."
  exit 1
fi

echo "=== Integral operator / Hilbert-Schmidt source files ==="
rg --files "$mathlib_root" |
  rg -i 'HilbertSchmidt|IntegralOperator|Kernel|CompactOperator|L2Space' ||
  true

echo "=== L2 membership and product-integrability interfaces ==="
rg -n -C 3 \
  'memLp_two_iff|integrable_sq_norm|integrable_norm_sq|integrable_prod_iff|integrable_prod_left_ae|integrable_prod_right_ae' \
  "$mathlib_root/MeasureTheory" ||
  true

echo "=== Integral-operator construction interfaces ==="
rg -n -C 3 \
  '(def|theorem|lemma).*([Ii]ntegralOperator|[Hh]ilbertSchmidt|integral.*[Cc]ompact|[Cc]ompact.*integral)' \
  "$mathlib_root/Analysis" "$mathlib_root/MeasureTheory" ||
  true

echo "PASS: half-line space checks and operator API source audit"
