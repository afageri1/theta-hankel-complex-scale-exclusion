#!/usr/bin/env bash
set -euo pipefail

if [[ ! -f lakefile.lean && ! -f lakefile.toml ]]; then
  echo "STOP: run from the hodgeproof-hp project root."
  exit 1
fi

lake build HodgeProofHP.Stage4ThetaHankelActionMeasurability

target="HodgeProofHP/Stage4HankelCauchySchwarzApiAudit.lean"

if [[ -f "$target" ]]; then
  backup="${target}.before_create_$(date +%Y%m%d_%H%M%S)_$$"
  cp -p "$target" "$backup"
  echo "BACKUP: $backup"
fi

cat > "$target" <<'LEAN'
import HodgeProofHP.Stage4ThetaHankelActionMeasurability

/-!
API audit for the Cauchy-Schwarz estimate and L2 norm formula.
-/

noncomputable section

namespace HodgeProofHP

open MeasureTheory
open scoped ENNReal

#check norm_inner_le_norm
#check MemLp.toLp
#check Lp.memLp
#check memLp_two_iff_integrable_sq_norm
#check hpThetaHankelKernel_row_memLp_ae
#check hpThetaHankelActionFunction_aestronglyMeasurable
#check hpThetaHankelRowEnergy_integrable

end HodgeProofHP
LEAN

lake env lean "$target"

mathlib_root=".lake/packages/mathlib/Mathlib"
l2_source="$mathlib_root/MeasureTheory/Function/L2Space.lean"

if [[ ! -f "$l2_source" ]]; then
  echo "STOP: L2Space source not found."
  exit 1
fi

echo "=== L2Space: norm, inner product, and integrability ==="
sed -n '1,240p' "$l2_source"

echo "=== Cauchy-Schwarz and integral norm formulas ==="
rg -n -C 5 \
  'integral_mul_le_Lp_mul_Lq|integral_mul_le.*sqrt|integral_norm_mul_le|norm_sq_eq_integral|integral_norm_sq_eq|norm_toLp|inner_eq_integral' \
  "$mathlib_root/MeasureTheory" \
  "$mathlib_root/Analysis/InnerProductSpace" ||
  true

echo "PASS: Hankel Cauchy-Schwarz API audit"
