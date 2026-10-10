#!/usr/bin/env bash
set -euo pipefail

target="HodgeProofHP/Stage4SecondOrderIntegrationByParts.lean"

if [ ! -f lakefile.lean ] && [ ! -f lakefile.toml ]; then
  echo "STOP: run from the hodgeproof-hp repository root."
  exit 1
fi

lake build HodgeProofHP.Stage4ThetaIntegrationByPartsApiAudit

if [ -f "$target" ]; then
  stamp="$(date +%Y%m%d_%H%M%S)"
  cp -p "$target" "${target}.before_${stamp}_$$"
fi

cat > "$target" <<'LEAN'
import HodgeProofHP.Stage4ThetaProfileZeroBoundary
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
Second-order integration by parts on a finite interval.
Derivative and integrability hypotheses remain explicit.
This lemma will be applied to the theta profile and complex cosine.
-/

open MeasureTheory

namespace HodgeProofHP

theorem hpSecondOrderIntegrationByParts
    (f f₁ f₂ c c₁ c₂ : ℝ → ℂ) (R : ℝ)
    (hf : ∀ x : ℝ, HasDerivAt f (f₁ x) x)
    (hf₁ : ∀ x : ℝ, HasDerivAt f₁ (f₂ x) x)
    (hc : ∀ x : ℝ, HasDerivAt c (c₁ x) x)
    (hc₁ : ∀ x : ℝ, HasDerivAt c₁ (c₂ x) x)
    (hif₁ : IntervalIntegrable f₁ volume 0 R)
    (hif₂ : IntervalIntegrable f₂ volume 0 R)
    (hic₁ : IntervalIntegrable c₁ volume 0 R)
    (hic₂ : IntervalIntegrable c₂ volume 0 R) :
    (∫ x in (0 : ℝ)..R, f₂ x * c x) =
      f₁ R * c R - f₁ 0 * c 0 -
        f R * c₁ R + f 0 * c₁ 0 +
          ∫ x in (0 : ℝ)..R, f x * c₂ x := by
  have hfirst :
      (∫ x in (0 : ℝ)..R, f₂ x * c x) =
        f₁ R * c R - f₁ 0 * c 0 -
          ∫ x in (0 : ℝ)..R, f₁ x * c₁ x := by
    simpa only [mul_comm] using
      (intervalIntegral.integral_mul_deriv_eq_deriv_mul
        (fun x _ => hc x)
        (fun x _ => hf₁ x)
        hic₁ hif₂)
  have hsecond :
      (∫ x in (0 : ℝ)..R, f₁ x * c₁ x) =
        f R * c₁ R - f 0 * c₁ 0 -
          ∫ x in (0 : ℝ)..R, f x * c₂ x := by
    simpa only [mul_comm] using
      (intervalIntegral.integral_mul_deriv_eq_deriv_mul
        (fun x _ => hc₁ x)
        (fun x _ => hf x)
        hic₂ hif₁)
  rw [hsecond] at hfirst
  calc
    (∫ x in (0 : ℝ)..R, f₂ x * c x) =
        f₁ R * c R - f₁ 0 * c 0 -
          (f R * c₁ R - f 0 * c₁ 0 -
            ∫ x in (0 : ℝ)..R, f x * c₂ x) := hfirst
    _ = _ := by ring

#print axioms hpSecondOrderIntegrationByParts

end HodgeProofHP
LEAN

lake env lean "$target"
lake build HodgeProofHP.Stage4SecondOrderIntegrationByParts

echo "PASS: finite-interval second-order integration by parts."
