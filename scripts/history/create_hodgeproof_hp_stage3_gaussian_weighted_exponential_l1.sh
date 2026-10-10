#!/usr/bin/env bash
set -euo pipefail

target="HodgeProofHP/Stage3GaussianWeightedExponentialL1.lean"

if [ -f "$target" ]; then
  cp "$target" "${target}.before_weighted_exponential_l1"
fi

cat > "$target" <<'LEAN'
import HodgeProofHP.Stage3GaussianExponentialIntegrability

/-! Exponential L1 bounds for the complex Gaussian-weighted L2 function. -/

open MeasureTheory

namespace HodgeProofHP

theorem hpGaussianGroundFunction_norm_eq_real (x : ℝ) :
    ‖hpGaussianGroundFunction x‖ =
      Real.exp (-(x ^ 2 / 2)) := by
  rw [hpGaussianGroundFunction_eq_real]
  simp only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]

theorem hpGaussianWeightedL2Function_exponential_norm_integrable
    (a : ℝ) (v : HPSpace) :
    Integrable
      (fun x : ℝ =>
        Real.exp (a * |x|) * ‖hpGaussianWeightedL2Function v x‖)
      volume := by
  simpa only [hpGaussianWeightedL2Function, norm_mul,
    hpGaussianGroundFunction_norm_eq_real, mul_assoc] using
    hpGaussianExponentialWeight_mul_L2_norm_integrable a v

theorem hpGaussianWeightedL2Function_exponential_integrable
    (a : ℝ) (v : HPSpace) :
    Integrable
      (fun x : ℝ =>
        (Real.exp (a * |x|) : ℂ) *
          hpGaussianWeightedL2Function v x)
      volume := by
  have hc :
      Continuous
        (fun x : ℝ =>
          (Real.exp (a * |x|) : ℂ) *
            hpGaussianGroundFunction x) := by
    simp only [hpGaussianGroundFunction_eq_real]
    fun_prop
  have hm :
      AEStronglyMeasurable
        (fun x : ℝ =>
          (Real.exp (a * |x|) : ℂ) *
            hpGaussianWeightedL2Function v x)
        volume := by
    have h :=
      hc.aestronglyMeasurable.mul
        (MeasureTheory.Lp.memLp v).aestronglyMeasurable
    change AEStronglyMeasurable
      (fun x : ℝ =>
        ((Real.exp (a * |x|) : ℂ) *
          hpGaussianGroundFunction x) * v x)
      volume at h
    simpa only [hpGaussianWeightedL2Function, mul_assoc] using h
  apply
    (hpGaussianWeightedL2Function_exponential_norm_integrable a v).mono' hm
  filter_upwards with x
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), le_refl]

#print axioms hpGaussianGroundFunction_norm_eq_real
#print axioms hpGaussianWeightedL2Function_exponential_norm_integrable
#print axioms hpGaussianWeightedL2Function_exponential_integrable

end HodgeProofHP
LEAN

lake env lean "$target"
lake build HodgeProofHP.Stage3GaussianWeightedExponentialL1
