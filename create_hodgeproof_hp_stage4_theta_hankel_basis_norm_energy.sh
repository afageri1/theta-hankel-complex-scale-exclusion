#!/usr/bin/env bash
set -euo pipefail

lake build HodgeProofHP.Stage4ThetaHankelBasisEnergy

target="HodgeProofHP/Stage4ThetaHankelBasisNormEnergy.lean"

if [ -f "$target" ]; then
  cp -p "$target" "$target.before_update_$(date +%Y%m%d_%H%M%S)"
fi

cat > "$target" <<'LEAN'
import HodgeProofHP.Stage4ThetaHankelBasisEnergy
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
Conversion of action energy into operator norm energy.
This module does not define an operator trace or a Fredholm determinant.
-/

namespace HodgeProofHP

open MeasureTheory

theorem hpThetaHankelAction_sq_lintegral_eq_ofReal_norm_sq
    (f : HPThetaHankelSpace) :
    (∫⁻ x,
      ENNReal.ofReal (‖hpThetaHankelActionFunction f x‖ ^ 2)
        ∂hpThetaHankelMeasure) =
      ENNReal.ofReal (‖hpThetaHankelOperator f‖ ^ 2) := by
  have hnonneg :
      0 ≤ᵐ[hpThetaHankelMeasure]
        (fun x => ‖hpThetaHankelActionFunction f x‖ ^ 2) :=
    Filter.Eventually.of_forall
      (fun x => sq_nonneg ‖hpThetaHankelActionFunction f x‖)
  calc
    _ = ENNReal.ofReal
        (∫ x, ‖hpThetaHankelActionFunction f x‖ ^ 2
          ∂hpThetaHankelMeasure) :=
      (ofReal_integral_eq_lintegral_ofReal
        (hpThetaHankelActionFunction_norm_sq_integrable f)
        hnonneg).symm
    _ = ENNReal.ofReal (‖hpThetaHankelOperator f‖ ^ 2) :=
      congrArg ENNReal.ofReal
        (hpThetaHankelOperator_norm_sq_eq_action_integral f).symm

theorem hpThetaHankelRowEnergy_lintegral_eq_ofReal_integral :
    (∫⁻ x, ENNReal.ofReal (hpThetaHankelRowEnergy x)
      ∂hpThetaHankelMeasure) =
      ENNReal.ofReal
        (∫ x, hpThetaHankelRowEnergy x ∂hpThetaHankelMeasure) := by
  exact
    (ofReal_integral_eq_lintegral_ofReal
      hpThetaHankelRowEnergy_integrable
      (Filter.Eventually.of_forall
        (fun x => hpThetaHankelRowEnergy_nonneg x))).symm

theorem hpThetaHankelBasis_norm_sq_tsum_eq_rowEnergy_integral
    {ι : Type*} [Countable ι]
    (b : HilbertBasis ι ℂ HPThetaHankelSpace) :
    (∑' i, ENNReal.ofReal (‖hpThetaHankelOperator (b i)‖ ^ 2)) =
      ENNReal.ofReal
        (∫ x, hpThetaHankelRowEnergy x ∂hpThetaHankelMeasure) := by
  calc
    _ = ∑' i,
        ∫⁻ x,
          ENNReal.ofReal
            (‖hpThetaHankelActionFunction (b i) x‖ ^ 2)
          ∂hpThetaHankelMeasure := by
      apply tsum_congr
      intro i
      exact
        (hpThetaHankelAction_sq_lintegral_eq_ofReal_norm_sq
          (b i)).symm
    _ = ∫⁻ x, ENNReal.ofReal (hpThetaHankelRowEnergy x)
        ∂hpThetaHankelMeasure :=
      hpThetaHankelBasis_tsum_lintegral_eq_rowEnergy b
    _ = _ :=
      hpThetaHankelRowEnergy_lintegral_eq_ofReal_integral

theorem hpThetaHankelBasis_norm_sq_tsum_lt_top
    {ι : Type*} [Countable ι]
    (b : HilbertBasis ι ℂ HPThetaHankelSpace) :
    (∑' i, ENNReal.ofReal
      (‖hpThetaHankelOperator (b i)‖ ^ 2)) < ⊤ := by
  rw [hpThetaHankelBasis_norm_sq_tsum_eq_rowEnergy_integral b]
  exact ENNReal.ofReal_lt_top

#print axioms hpThetaHankelAction_sq_lintegral_eq_ofReal_norm_sq
#print axioms hpThetaHankelRowEnergy_lintegral_eq_ofReal_integral
#print axioms hpThetaHankelBasis_norm_sq_tsum_eq_rowEnergy_integral
#print axioms hpThetaHankelBasis_norm_sq_tsum_lt_top

end HodgeProofHP
LEAN

lake env lean "$target"
lake build HodgeProofHP.Stage4ThetaHankelBasisNormEnergy

printf '%s\n' 'PASS: Stage4ThetaHankelBasisNormEnergy'
