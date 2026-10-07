import HodgeProofHP.Stage5ThetaJensenTailIntegrals
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-!
# Numerical bounds for the theta moment tails

Taylor lower bounds and rational bounds for pi certify both tails
above 1 by 1/50000000. No JSON data or moment inequality is assumed.
The finite-interval moment certificates remain a separate obligation.
-/

noncomputable section

open MeasureTheory

namespace HodgeProofHP

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor evaluation by norm_num needs a larger tactic budget.
theorem hpThetaJensen_exp_two_lower :
    (7389 / 1000 : ℝ) ≤ Real.exp 2 := by
  exact hpThetaTrace_exp_lower_of_taylor
    2 (7389 / 1000 : ℝ) 12 (by norm_num)
    (by norm_num [hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial])

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor evaluation by norm_num needs a larger tactic budget.
theorem hpThetaJensen_exp_eighteenSeven_lower :
    (128000000 : ℝ) ≤ Real.exp (187 / 10 : ℝ) := by
  exact hpThetaTrace_exp_lower_of_taylor
    (187 / 10 : ℝ) 128000000 32 (by norm_num)
    (by norm_num [hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial])

theorem hpThetaJensen_pi_exp_two_lower :
    (116 / 5 : ℝ) ≤ Real.pi * Real.exp 2 := by
  have hpi : (157 / 50 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d2
    linarith
  have h := mul_le_mul hpi hpThetaJensen_exp_two_lower
    (by norm_num : (0 : ℝ) ≤ 7389 / 1000) (le_of_lt Real.pi_pos)
  norm_num at h
  linarith

theorem hpThetaJensenKernelTailRate_one_ge_fortyOne :
    (41 : ℝ) ≤ hpThetaJensenKernelTailRate 1 := by
  have h := hpThetaJensen_pi_exp_two_lower
  unfold hpThetaJensenKernelTailRate
  norm_num only [mul_one]
  linarith

theorem hpThetaJensenKernelTailAmplitude_one_le :
    hpThetaJensenKernelTailAmplitude 1 ≤ (1 / 1600000 : ℝ) := by
  have hpi : Real.pi ≤ (63 / 20 : ℝ) := by
    have h := Real.pi_lt_d2
    linarith
  have hsq := pow_le_pow_left₀ (le_of_lt Real.pi_pos) hpi 2
  have hpref : (12183 / 12151 : ℝ) * (8 * Real.pi ^ 2) ≤ 80 := by
    nlinarith [hsq]
  have harg : (9 / 2 : ℝ) * 1 - Real.pi * Real.exp (2 * 1) ≤
      -(187 / 10 : ℝ) := by
    norm_num only [mul_one]
    linarith [hpThetaJensen_pi_exp_two_lower]
  have hinv : (Real.exp (187 / 10 : ℝ))⁻¹ ≤ (1 / 128000000 : ℝ) := by
    rw [← one_div]
    apply (div_le_div_iff₀ (Real.exp_pos _) (by norm_num : (0 : ℝ) < 128000000)).2
    simpa only [one_mul] using hpThetaJensen_exp_eighteenSeven_lower
  have he : Real.exp ((9 / 2 : ℝ) * 1 - Real.pi * Real.exp (2 * 1)) ≤
      (1 / 128000000 : ℝ) := by
    have h := Real.exp_le_exp.mpr harg
    rw [Real.exp_neg] at h
    exact le_trans h hinv
  have h := mul_le_mul hpref he (le_of_lt (Real.exp_pos _))
    (by norm_num : (0 : ℝ) ≤ 80)
  unfold hpThetaJensenKernelTailAmplitude
  norm_num at h ⊢
  exact h

theorem hpThetaJensenZeroTailUpper_le_twoEminusEight :
    hpThetaJensenZeroTailUpper ≤ (1 / 50000000 : ℝ) := by
  unfold hpThetaJensenZeroTailUpper
  apply (div_le_iff₀ (hpThetaJensenKernelTailRate_pos 1 (by norm_num))).2
  have hA := hpThetaJensenKernelTailAmplitude_one_le
  have hk := hpThetaJensenKernelTailRate_one_ge_fortyOne
  linarith

theorem hpThetaJensenFourthTailUpper_le_twoEminusEight :
    hpThetaJensenFourthTailUpper ≤ (1 / 50000000 : ℝ) := by
  unfold hpThetaJensenFourthTailUpper
  apply (div_le_iff₀ (sub_pos.mpr hpThetaJensenKernelTailRate_one_gt_four)).2
  have hA := hpThetaJensenKernelTailAmplitude_one_le
  have hk := hpThetaJensenKernelTailRate_one_ge_fortyOne
  linarith

theorem hpThetaJensen_zeroMoment_tail_le_twoEminusEight :
    (∫ u : ℝ in Set.Ioi 1, hpRiemannThetaDifferentialKernel u) ≤
      (1 / 50000000 : ℝ) := by
  exact le_trans hpThetaJensen_zeroMoment_tail_le
    hpThetaJensenZeroTailUpper_le_twoEminusEight

theorem hpThetaJensen_fourthMoment_tail_le_twoEminusEight :
    (∫ u : ℝ in Set.Ioi 1, u ^ 4 * hpRiemannThetaDifferentialKernel u) ≤
      (1 / 50000000 : ℝ) := by
  exact le_trans hpThetaJensen_fourthMoment_tail_le
    hpThetaJensenFourthTailUpper_le_twoEminusEight

#print axioms hpThetaJensen_exp_two_lower
#print axioms hpThetaJensen_exp_eighteenSeven_lower
#print axioms hpThetaJensen_pi_exp_two_lower
#print axioms hpThetaJensenKernelTailRate_one_ge_fortyOne
#print axioms hpThetaJensenKernelTailAmplitude_one_le
#print axioms hpThetaJensenZeroTailUpper_le_twoEminusEight
#print axioms hpThetaJensenFourthTailUpper_le_twoEminusEight
#print axioms hpThetaJensen_zeroMoment_tail_le_twoEminusEight
#print axioms hpThetaJensen_fourthMoment_tail_le_twoEminusEight

end HodgeProofHP
