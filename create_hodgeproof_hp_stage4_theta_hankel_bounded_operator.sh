#!/usr/bin/env bash
set -euo pipefail

if [[ ! -f lakefile.lean && ! -f lakefile.toml ]]; then
  echo "ERROR: Run from the hodgeproof-hp project root."
  exit 1
fi

lake build HodgeProofHP.Stage4ThetaHankelLinearity

target="HodgeProofHP/Stage4ThetaHankelBoundedOperator.lean"
mkdir -p HodgeProofHP

if [[ -f "$target" ]]; then
  backup="${target}.before_create_$(date +%Y%m%d_%H%M%S)_$$"
  cp -p "$target" "$backup"
  echo "BACKUP: $backup"
fi

cat > "$target" <<'LEAN'
import HodgeProofHP.Stage4ThetaHankelLinearity

/-!
An L² norm bound for the Hankel action and its construction
as a continuous complex-linear operator.
-/

noncomputable section

namespace HodgeProofHP

open MeasureTheory
open scoped ENNReal

def hpThetaHankelTotalEnergy : ℝ :=
  ∫ x, hpThetaHankelRowEnergy x ∂hpThetaHankelMeasure

theorem hpThetaHankelTotalEnergy_nonneg :
    0 ≤ hpThetaHankelTotalEnergy := by
  unfold hpThetaHankelTotalEnergy
  exact integral_nonneg hpThetaHankelRowEnergy_nonneg

theorem hpThetaHankelSpace_norm_sq_eq_integral
    (f : HPThetaHankelSpace) :
    ‖f‖ ^ 2 =
      ∫ x, ‖f x‖ ^ 2 ∂hpThetaHankelMeasure := by
  have hcast :
      ((‖f‖ ^ 2 : ℝ) : ℂ) =
        ((∫ x, ‖f x‖ ^ 2 ∂hpThetaHankelMeasure : ℝ) : ℂ) := by
    calc
      ((‖f‖ ^ 2 : ℝ) : ℂ) = inner ℂ f f := by
        rw [inner_self_eq_norm_sq_to_K]
        simp only [Complex.ofReal_pow] <;> rfl
      _ = ∫ x, ((‖f x‖ ^ 2 : ℝ) : ℂ)
          ∂hpThetaHankelMeasure := by
        rw [MeasureTheory.L2.inner_def]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun x => by
          change inner ℂ (f x) (f x) =
            ((‖f x‖ ^ 2 : ℝ) : ℂ)
          rw [inner_self_eq_norm_sq_to_K]
          simp only [Complex.ofReal_pow] <;> rfl)
      _ = ((∫ x, ‖f x‖ ^ 2 ∂hpThetaHankelMeasure : ℝ) : ℂ) := by
        norm_cast
  exact_mod_cast hcast

theorem hpThetaHankelActionL2_norm_sq_le
    (f : HPThetaHankelSpace) :
    ‖hpThetaHankelActionL2 f‖ ^ 2 ≤
      hpThetaHankelTotalEnergy * ‖f‖ ^ 2 := by
  have hmajor :
      Integrable (fun x => hpThetaHankelRowEnergy x * ‖f‖ ^ 2)
        hpThetaHankelMeasure :=
    hpThetaHankelRowEnergy_integrable.mul_const (‖f‖ ^ 2)
  calc
    ‖hpThetaHankelActionL2 f‖ ^ 2 =
        ∫ x, ‖hpThetaHankelActionL2 f x‖ ^ 2
          ∂hpThetaHankelMeasure :=
      hpThetaHankelSpace_norm_sq_eq_integral _
    _ = ∫ x, ‖hpThetaHankelActionFunction f x‖ ^ 2
          ∂hpThetaHankelMeasure := by
      apply integral_congr_ae
      filter_upwards [hpThetaHankelActionL2_coeFn_ae f] with x hx
      rw [hx]
    _ ≤ ∫ x, hpThetaHankelRowEnergy x * ‖f‖ ^ 2
          ∂hpThetaHankelMeasure :=
      integral_mono_ae
        (hpThetaHankelActionFunction_norm_sq_integrable f)
        hmajor
        (hpThetaHankelActionFunction_norm_sq_le_ae f)
    _ = hpThetaHankelTotalEnergy * ‖f‖ ^ 2 := by
      unfold hpThetaHankelTotalEnergy
      rw [integral_mul_const]

theorem hpThetaHankelActionL2_norm_le
    (f : HPThetaHankelSpace) :
    ‖hpThetaHankelActionL2 f‖ ≤
      Real.sqrt hpThetaHankelTotalEnergy * ‖f‖ := by
  have hsq := hpThetaHankelActionL2_norm_sq_le f
  have hsqrt := Real.sq_sqrt hpThetaHankelTotalEnergy_nonneg
  have hnonneg :
      0 ≤ Real.sqrt hpThetaHankelTotalEnergy * ‖f‖ :=
    mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg f)
  have hbound :
      ‖hpThetaHankelActionL2 f‖ ^ 2 ≤
        (Real.sqrt hpThetaHankelTotalEnergy * ‖f‖) ^ 2 := by
    rw [mul_pow, hsqrt]
    exact hsq
  nlinarith [norm_nonneg (hpThetaHankelActionL2 f)]

/-- The bounded Hankel integral operator on the half-line L² space. -/
def hpThetaHankelOperator :
    HPThetaHankelSpace →L[ℂ] HPThetaHankelSpace :=
  hpThetaHankelLinearMap.mkContinuous
    (Real.sqrt hpThetaHankelTotalEnergy)
    (fun f => hpThetaHankelActionL2_norm_le f)

theorem hpThetaHankelOperator_apply
    (f : HPThetaHankelSpace) :
    hpThetaHankelOperator f = hpThetaHankelActionL2 f := rfl

theorem hpThetaHankelOperator_coeFn_ae
    (f : HPThetaHankelSpace) :
    (fun x => hpThetaHankelOperator f x) =ᵐ[hpThetaHankelMeasure]
      hpThetaHankelActionFunction f :=
  hpThetaHankelActionL2_coeFn_ae f

#print axioms hpThetaHankelTotalEnergy_nonneg
#print axioms hpThetaHankelSpace_norm_sq_eq_integral
#print axioms hpThetaHankelActionL2_norm_sq_le
#print axioms hpThetaHankelActionL2_norm_le
#print axioms hpThetaHankelOperator
#print axioms hpThetaHankelOperator_apply
#print axioms hpThetaHankelOperator_coeFn_ae

end HodgeProofHP
LEAN

lake env lean "$target"
lake build HodgeProofHP.Stage4ThetaHankelBoundedOperator
echo "PASS: Stage4ThetaHankelBoundedOperator"
