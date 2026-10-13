/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenCNVLocalPositivity

/-!
# A second kernel derivative lower bound on an explicit interval

The first Gaussian second derivative is bounded below by -35 for
0 <= u <= 1/1000000. The remaining terms are nonnegative on the entire
nonnegative half-line. The actual kernel therefore satisfies the same
lower bound on this explicit interval. This is a quantitative ingredient;
an explicit CNV positivity radius is not established here.
-/
noncomputable section
namespace HodgeProofHP

theorem hpThetaCNV_exp_twoMicro_upper :
    Real.exp (1 / 500000 : ℝ) ≤ (1000003 / 1000000 : ℝ) := by
  exact hpThetaTrace_exp_upper_of_taylor (1 / 500000) (1000003 / 1000000) 6
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial])

theorem hpThetaCNV_exp_halfMicro_upper :
    Real.exp (1 / 2000000 : ℝ) ≤ (1000001 / 1000000 : ℝ) := by
  exact hpThetaTrace_exp_upper_of_taylor (1 / 2000000) (1000001 / 1000000) 6
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial])

theorem hpThetaCNV_firstParameter_nearZero_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (0 : ℝ) (1 / 1000000)) :
    (31415 / 10000 : ℝ) ≤ Real.pi * Real.exp (2 * u) ∧
      Real.pi * Real.exp (2 * u) ≤ (314161 / 100000 : ℝ) := by
  have hpiL : (31415 / 10000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d4
    linarith
  have hpiU : Real.pi ≤ (3927 / 1250 : ℝ) := by
    have h := Real.pi_lt_d4
    linarith
  have heL : (1 : ℝ) ≤ Real.exp (2 * u) := by
    simpa only [Real.exp_zero] using
      Real.exp_le_exp.mpr (show (0 : ℝ) ≤ 2 * u by linarith [hu.1])
  have heU : Real.exp (2 * u) ≤ (1000003 / 1000000 : ℝ) :=
    (Real.exp_le_exp.mpr (by linarith [hu.2])).trans hpThetaCNV_exp_twoMicro_upper
  have hL := mul_le_mul_of_nonneg_left heL Real.pi_pos.le
  have hU := mul_le_mul hpiU heU (Real.exp_nonneg _) (by norm_num)
  constructor <;> nlinarith [hL, hU]

theorem hpThetaCNV_secondDerivative_firstTerm_nearZero_ge_neg35 (u : ℝ)
    (hu : u ∈ Set.Icc (0 : ℝ) (1 / 1000000)) :
    (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  let q : ℝ := Real.pi * Real.exp (2 * u)
  have hq := hpThetaCNV_firstParameter_nearZero_bounds u hu
  change (31415 / 10000 : ℝ) ≤ q ∧ q ≤ (314161 / 100000 : ℝ) at hq
  have hq0 : 0 ≤ q := by linarith [hq.1]
  have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 31415 / 10000) hq.1 2
  have h4L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 31415 / 10000) hq.1 4
  have h3U := pow_le_pow_left₀ hq0 hq.2 3
  have hpoly : (-404 : ℝ) ≤
      16 * q ^ 4 - 112 * q ^ 3 + 165 * q ^ 2 - (75 / 2 : ℝ) * q := by
    nlinarith [h2L, h4L, h3U, hq.2]
  have heL : (1 : ℝ) ≤ Real.exp (2 * u) := by
    simpa only [Real.exp_zero] using
      Real.exp_le_exp.mpr (show (0 : ℝ) ≤ 2 * u by linarith [hu.1])
  have hscaled := mul_le_mul_of_nonneg_left heL Real.pi_pos.le
  have he : Real.exp (u / 2 - Real.pi * Real.exp (2 * u)) ≤
      (1000001 / 1000000 : ℝ) * (433 / 10000) := by
    calc
      _ ≤ Real.exp (1 / 2000000 : ℝ) * Real.exp (-Real.pi) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        nlinarith [hu.2, hscaled]
      _ ≤ _ := mul_le_mul hpThetaCNV_exp_halfMicro_upper hpThetaCNV_exp_neg_pi_upper
        (Real.exp_nonneg _) (by norm_num)
  have hp : hpThetaGaussianProfile Real.pi u ≤
      2 * ((1000001 / 1000000 : ℝ) * (433 / 10000)) := by
    exact mul_le_mul_of_nonneg_left he (by norm_num)
  have heq : hpThetaGaussianKernelSecondDerivativeTerm Real.pi u =
      (16 * q ^ 4 - 112 * q ^ 3 + 165 * q ^ 2 - (75 / 2 : ℝ) * q) *
        hpThetaGaussianProfile Real.pi u := by
    unfold hpThetaGaussianKernelSecondDerivativeTerm
    dsimp [q]
    ring
  rw [heq]
  calc
    (-35 : ℝ) ≤ (-404 : ℝ) *
        (2 * ((1000001 / 1000000 : ℝ) * (433 / 10000))) := by norm_num
    _ ≤ (-404 : ℝ) * hpThetaGaussianProfile Real.pi u := by linarith [hp]
    _ ≤ _ := mul_le_mul_of_nonneg_right hpoly (hpThetaGaussianProfile_pos Real.pi u).le

theorem hpThetaCNV_secondDerivative_tailTerm_nonneg_nonnegative
    (n : ℕ) (u : ℝ) (hu : 0 ≤ u) :
    0 ≤ hpThetaGaussianKernelSecondDerivativeTerm
      (hpThetaGaussianParameter (n + 1)) u := by
  have hk : (2 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) + 1 := by
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    push_cast
    linarith
  have hs := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hk 2
  have hm := mul_le_mul Real.pi_gt_three.le hs (by norm_num) Real.pi_pos.le
  have ha : (7 : ℝ) ≤ hpThetaGaussianParameter (n + 1) := by
    unfold hpThetaGaussianParameter
    nlinarith [hm]
  let q : ℝ := hpThetaGaussianParameter (n + 1) * Real.exp (2 * u)
  have he : (1 : ℝ) ≤ Real.exp (2 * u) := by
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (show (0 : ℝ) ≤ 2 * u by linarith)
  have hmul := mul_le_mul_of_nonneg_left he (hpThetaGaussianParameter_nonneg (n + 1))
  have hq : (7 : ℝ) ≤ q := by dsimp [q]; nlinarith [hmul]
  have hp := hpThetaCNV_secondDerivativeFactor_nonneg q hq
  have heq : hpThetaGaussianKernelSecondDerivativeTerm (hpThetaGaussianParameter (n + 1)) u =
      (16 * q ^ 4 - 112 * q ^ 3 + 165 * q ^ 2 - (75 / 2 : ℝ) * q) *
        hpThetaGaussianProfile (hpThetaGaussianParameter (n + 1)) u := by
    unfold hpThetaGaussianKernelSecondDerivativeTerm
    dsimp [q]
    ring
  rw [heq]
  exact mul_nonneg hp (hpThetaGaussianProfile_pos (hpThetaGaussianParameter (n + 1)) u).le

theorem hpThetaPhi_secondDeriv_ge_neg35_nearZero (u : ℝ)
    (hu : u ∈ Set.Icc (0 : ℝ) (1 / 1000000)) :
    (-35 : ℝ) ≤ deriv (deriv hpRiemannThetaDifferentialKernel) u := by
  have hs := hpThetaGaussianKernelSecondDerivativeTerm_summable u
  have htail : 0 ≤ ∑' n : ℕ,
      hpThetaGaussianKernelSecondDerivativeTerm (hpThetaGaussianParameter (n + 1)) u :=
    tsum_nonneg (fun n => hpThetaCNV_secondDerivative_tailTerm_nonneg_nonnegative n u hu.1)
  have hfirst := hpThetaCNV_secondDerivative_firstTerm_nearZero_ge_neg35 u hu
  have hparam : hpThetaGaussianParameter 0 = Real.pi := by simp [hpThetaGaussianParameter]
  rw [hpThetaPhi_secondDeriv_eq_kernelSeries, hs.tsum_eq_zero_add, hparam]
  linarith

#print axioms hpThetaCNV_exp_twoMicro_upper
#print axioms hpThetaCNV_exp_halfMicro_upper
#print axioms hpThetaCNV_firstParameter_nearZero_bounds
#print axioms hpThetaCNV_secondDerivative_firstTerm_nearZero_ge_neg35
#print axioms hpThetaCNV_secondDerivative_tailTerm_nonneg_nonnegative
#print axioms hpThetaPhi_secondDeriv_ge_neg35_nearZero
end HodgeProofHP
