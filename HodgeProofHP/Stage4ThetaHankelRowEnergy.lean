import HodgeProofHP.Stage4ThetaHankelCauchySchwarz

/-!
Identify the squared L² norm of a kernel row with its energy,
and derive the squared Cauchy–Schwarz estimate.
-/

noncomputable section

namespace HodgeProofHP

open MeasureTheory
open scoped ENNReal

theorem hpThetaHankelRowL2_norm_sq (x : ℝ)
    (hx : MemLp (fun y => hpThetaHankelKernel x y)
      2 hpThetaHankelMeasure) :
    ‖hpThetaHankelRowL2 x hx‖ ^ 2 =
      hpThetaHankelRowEnergy x := by
  have hcast :
      ((‖hpThetaHankelRowL2 x hx‖ ^ 2 : ℝ) : ℂ) =
        (hpThetaHankelRowEnergy x : ℂ) := by
    calc
      ((‖hpThetaHankelRowL2 x hx‖ ^ 2 : ℝ) : ℂ) =
          inner ℂ (hpThetaHankelRowL2 x hx)
            (hpThetaHankelRowL2 x hx) := by
        rw [inner_self_eq_norm_sq_to_K]
        simp only [Complex.ofReal_pow] <;> rfl
      _ = ∫ y, ((‖hpThetaHankelKernel x y‖ ^ 2 : ℝ) : ℂ)
          ∂hpThetaHankelMeasure := by
        rw [MeasureTheory.L2.inner_def]
        apply integral_congr_ae
        filter_upwards [hpThetaHankelRowL2_coeFn_ae x hx] with y hy
        rw [hy, inner_self_eq_norm_sq_to_K]
        simp only [Complex.ofReal_pow] <;> rfl
      _ = (hpThetaHankelRowEnergy x : ℂ) := by
        unfold hpThetaHankelRowEnergy
        norm_cast
  exact_mod_cast hcast

theorem hpThetaHankelActionFunction_norm_sq_le
    (f : HPThetaHankelSpace) (x : ℝ)
    (hx : MemLp (fun y => hpThetaHankelKernel x y)
      2 hpThetaHankelMeasure) :
    ‖hpThetaHankelActionFunction f x‖ ^ 2 ≤
      hpThetaHankelRowEnergy x * ‖f‖ ^ 2 := by
  have hle := hpThetaHankelActionFunction_norm_le f x hx
  have hsq := mul_le_mul hle hle
    (norm_nonneg (hpThetaHankelActionFunction f x))
    (mul_nonneg (norm_nonneg (hpThetaHankelRowL2 x hx))
      (norm_nonneg f))
  simpa only [← pow_two, mul_pow,
    hpThetaHankelRowL2_norm_sq x hx] using hsq

theorem hpThetaHankelActionFunction_norm_sq_le_ae
    (f : HPThetaHankelSpace) :
    ∀ᵐ x ∂hpThetaHankelMeasure,
      ‖hpThetaHankelActionFunction f x‖ ^ 2 ≤
        hpThetaHankelRowEnergy x * ‖f‖ ^ 2 := by
  filter_upwards [hpThetaHankelKernel_row_memLp_ae] with x hx
  exact hpThetaHankelActionFunction_norm_sq_le f x hx

#print axioms hpThetaHankelRowL2_norm_sq
#print axioms hpThetaHankelActionFunction_norm_sq_le
#print axioms hpThetaHankelActionFunction_norm_sq_le_ae

end HodgeProofHP
