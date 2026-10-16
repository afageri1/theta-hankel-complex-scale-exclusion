/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenCNVPositiveOnOneFiftieth

/-!
# Strict decrease of the actual kernel on [1/50, infinity)

Every differentiated Gaussian term is negative once its rescaled parameter
is at least 13/4. This holds for all terms at every t >= 1/50. Summability
allows the strict first-term bound and the nonpositive remaining series to
be combined. The result also extends the kernel upper bound of 2 to t >= 0.
Neither the derivative sign nor monotonicity proves far-field CNV positivity;
a quantitative weighted-tail comparison is still required.
-/
noncomputable section
namespace HodgeProofHP

theorem hpThetaCNV_far_parameter_ge_thirteen_fourths (n : ℕ) (t : ℝ)
    (ht : (1 / 50 : ℝ) ≤ t) :
    (13 / 4 : ℝ) ≤ hpThetaGaussianParameter n * Real.exp (2 * t) := by
  have hpiL : (157 / 50 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d2
    linarith
  have he : (26 / 25 : ℝ) ≤ Real.exp (2 * t) := by
    have h := Real.add_one_le_exp (2 * t)
    linarith
  have hparam : Real.pi ≤ hpThetaGaussianParameter n := by
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hsq : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith
    have h := mul_le_mul_of_nonneg_left hsq Real.pi_pos.le
    simpa only [hpThetaGaussianParameter, mul_one] using h
  calc
    (13 / 4 : ℝ) ≤ (157 / 50 : ℝ) * (26 / 25) := by norm_num
    _ ≤ Real.pi * Real.exp (2 * t) :=
      mul_le_mul hpiL he (by norm_num) Real.pi_pos.le
    _ ≤ _ := mul_le_mul_of_nonneg_right hparam (Real.exp_nonneg _)

theorem hpThetaCNV_firstDerivativeFactor_neg (q : ℝ) (hq : (13 / 4 : ℝ) ≤ q) :
    -8 * q ^ 3 + 30 * q ^ 2 - 15 * q < 0 := by
  have hh : 0 ≤ q - (13 / 4 : ℝ) := sub_nonneg.mpr hq
  have hpoly : 0 < 8 * q ^ 2 - 30 * q + 15 := by
    have heq : 8 * q ^ 2 - 30 * q + 15 =
        8 * (q - (13 / 4 : ℝ)) ^ 2 + 22 * (q - (13 / 4 : ℝ)) + 2 := by ring
    rw [heq]
    positivity
  have hqpos : 0 < q := by linarith
  have heq : -8 * q ^ 3 + 30 * q ^ 2 - 15 * q =
      (-q) * (8 * q ^ 2 - 30 * q + 15) := by ring
  rw [heq]
  exact mul_neg_of_neg_of_pos (neg_neg_of_pos hqpos) hpoly

theorem hpThetaCNV_kernelDerivativeTerm_neg_on_far (n : ℕ) (t : ℝ)
    (ht : (1 / 50 : ℝ) ≤ t) :
    hpThetaGaussianKernelDerivativeTerm (hpThetaGaussianParameter n) t < 0 := by
  have hq := hpThetaCNV_far_parameter_ge_thirteen_fourths n t ht
  have hfactor := hpThetaCNV_firstDerivativeFactor_neg
    (hpThetaGaussianParameter n * Real.exp (2 * t)) hq
  have heq : hpThetaGaussianKernelDerivativeTerm (hpThetaGaussianParameter n) t =
      (-8 * (hpThetaGaussianParameter n * Real.exp (2 * t)) ^ 3 +
        30 * (hpThetaGaussianParameter n * Real.exp (2 * t)) ^ 2 -
        15 * (hpThetaGaussianParameter n * Real.exp (2 * t))) *
          hpThetaGaussianProfile (hpThetaGaussianParameter n) t := by
    unfold hpThetaGaussianKernelDerivativeTerm
    ring
  rw [heq]
  exact mul_neg_of_neg_of_pos hfactor
    (hpThetaGaussianProfile_pos (hpThetaGaussianParameter n) t)

theorem hpThetaPhi_deriv_neg_on_far (t : ℝ) (ht : (1 / 50 : ℝ) ≤ t) :
    deriv hpRiemannThetaDifferentialKernel t < 0 := by
  have hs := hpThetaGaussianKernelDerivativeTerm_summable t
  have htail : (∑' n : ℕ,
      hpThetaGaussianKernelDerivativeTerm (hpThetaGaussianParameter (n + 1)) t) ≤ 0 :=
    tsum_nonpos (fun n => (hpThetaCNV_kernelDerivativeTerm_neg_on_far (n + 1) t ht).le)
  have hfirst := hpThetaCNV_kernelDerivativeTerm_neg_on_far 0 t ht
  rw [hpThetaPhi_deriv_eq_kernelSeries, hs.tsum_eq_zero_add]
  linarith

theorem hpThetaPhi_strictAntiOn_far :
    StrictAntiOn hpRiemannThetaDifferentialKernel (Set.Ici (1 / 50 : ℝ)) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici (1 / 50 : ℝ))
    hpRiemannThetaDifferentialKernel_continuous.continuousOn
  intro t ht
  exact hpThetaPhi_deriv_neg_on_far t (interior_subset ht)

theorem hpThetaPhi_le_two_on_nonnegative (t : ℝ) (ht : 0 ≤ t) :
    hpRiemannThetaDifferentialKernel t ≤ 2 := by
  by_cases hnear : t ≤ (1 / 50 : ℝ)
  · exact hpThetaPhi_le_two_on_oneFiftieth t ⟨ht, hnear⟩
  · have hfar : (1 / 50 : ℝ) < t := lt_of_not_ge hnear
    have hdec := hpThetaPhi_strictAntiOn_far
      (show (1 / 50 : ℝ) ∈ Set.Ici (1 / 50 : ℝ) by simp)
      (show t ∈ Set.Ici (1 / 50 : ℝ) by
        simpa only [Set.mem_Ici] using hfar.le) hfar
    exact hdec.le.trans (hpThetaPhi_le_two_on_oneFiftieth (1 / 50) (by
      constructor <;> norm_num))

#print axioms hpThetaCNV_far_parameter_ge_thirteen_fourths
#print axioms hpThetaCNV_firstDerivativeFactor_neg
#print axioms hpThetaCNV_kernelDerivativeTerm_neg_on_far
#print axioms hpThetaPhi_deriv_neg_on_far
#print axioms hpThetaPhi_strictAntiOn_far
#print axioms hpThetaPhi_le_two_on_nonnegative
end HodgeProofHP
