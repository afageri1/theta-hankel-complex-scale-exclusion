/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenCNVKernelZeroLower
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Lower bound for the actual second kernel derivative at zero

The first Gaussian term is bounded below by -35. All remaining second
derivative terms at zero are nonnegative, and the summable series therefore
gives Phi''(0) >= -35. This does not yet bound the weighted-tail product.
-/
noncomputable section
namespace HodgeProofHP

theorem hpThetaCNV_exp_neg_pi_upper :
    Real.exp (-Real.pi) ≤ (433 / 10000 : ℝ) := by
  have hlow : (231 / 10 : ℝ) ≤ Real.exp (31415 / 10000 : ℝ) := by
    exact hpThetaTrace_exp_lower_of_taylor (31415 / 10000) (231 / 10) 10
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hpi : (31415 / 10000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d4
    linarith
  have hlowpi := hlow.trans (Real.exp_le_exp.mpr hpi)
  have hprod := mul_le_mul_of_nonneg_right hlowpi (Real.exp_nonneg (-Real.pi))
  have hid : Real.exp Real.pi * Real.exp (-Real.pi) = 1 := by
    rw [← Real.exp_add]
    simp
  rw [hid] at hprod
  linarith

theorem hpThetaCNV_secondDerivativeFactor_nonneg (a : ℝ) (ha : 7 ≤ a) :
    0 ≤ 16 * a ^ 4 - 112 * a ^ 3 + 165 * a ^ 2 - (75 / 2 : ℝ) * a := by
  have ha0 : 0 ≤ a := by linarith
  have h1 : 0 ≤ 16 * a ^ 3 * (a - 7) :=
    mul_nonneg (by positivity) (sub_nonneg.mpr ha)
  have h2 : 0 ≤ a * (165 * a - (75 / 2 : ℝ)) :=
    mul_nonneg ha0 (by linarith)
  nlinarith [h1, h2]

theorem hpThetaCNV_secondDerivative_firstTerm_ge_neg35 :
    (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm
      (hpThetaGaussianParameter 0) 0 := by
  have hpiL : (31415 / 10000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d4
    linarith
  have hpiU : Real.pi ≤ (3927 / 1250 : ℝ) := by
    have h := Real.pi_lt_d4
    linarith
  have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 31415 / 10000) hpiL 2
  have h4L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 31415 / 10000) hpiL 4
  have h3U := pow_le_pow_left₀ Real.pi_pos.le hpiU 3
  have hpoly : (-404 : ℝ) ≤
      16 * Real.pi ^ 4 - 112 * Real.pi ^ 3 +
        165 * Real.pi ^ 2 - (75 / 2 : ℝ) * Real.pi := by
    nlinarith [h2L, h4L, h3U]
  have hbound : (-35 : ℝ) ≤
      (16 * Real.pi ^ 4 - 112 * Real.pi ^ 3 +
        165 * Real.pi ^ 2 - (75 / 2 : ℝ) * Real.pi) *
          (2 * Real.exp (-Real.pi)) := by
    calc
      (-35 : ℝ) ≤ (-404 : ℝ) * (2 * (433 / 10000)) := by norm_num
      _ ≤ (-404 : ℝ) * (2 * Real.exp (-Real.pi)) := by
        have h := hpThetaCNV_exp_neg_pi_upper
        linarith
      _ ≤ _ := mul_le_mul_of_nonneg_right hpoly (by positivity)
  simpa [hpThetaGaussianKernelSecondDerivativeTerm, hpThetaGaussianParameter,
    hpThetaGaussianProfile] using hbound

theorem hpThetaCNV_secondDerivative_tailTerm_nonneg (n : ℕ) :
    0 ≤ hpThetaGaussianKernelSecondDerivativeTerm
      (hpThetaGaussianParameter (n + 1)) 0 := by
  have hk : (2 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) + 1 := by
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    push_cast
    linarith
  have hs := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hk 2
  have hpi : (3 : ℝ) ≤ Real.pi := Real.pi_gt_three.le
  have hm := mul_le_mul hpi hs (by norm_num) Real.pi_pos.le
  have ha : (7 : ℝ) ≤ hpThetaGaussianParameter (n + 1) := by
    unfold hpThetaGaussianParameter
    nlinarith [hm]
  have hp := hpThetaCNV_secondDerivativeFactor_nonneg
    (hpThetaGaussianParameter (n + 1)) ha
  have h := mul_nonneg hp
    (hpThetaGaussianProfile_pos (hpThetaGaussianParameter (n + 1)) 0).le
  simpa only [hpThetaGaussianKernelSecondDerivativeTerm, mul_zero, Real.exp_zero,
    one_pow, mul_one] using h

theorem hpThetaPhi_secondDeriv_zero_ge_neg35 :
    (-35 : ℝ) ≤ deriv (deriv hpRiemannThetaDifferentialKernel) 0 := by
  have hs := hpThetaGaussianKernelSecondDerivativeTerm_summable 0
  have htail : 0 ≤ ∑' n : ℕ,
      hpThetaGaussianKernelSecondDerivativeTerm (hpThetaGaussianParameter (n + 1)) 0 :=
    tsum_nonneg hpThetaCNV_secondDerivative_tailTerm_nonneg
  rw [hpThetaPhi_secondDeriv_eq_kernelSeries, hs.tsum_eq_zero_add]
  have hfirst := hpThetaCNV_secondDerivative_firstTerm_ge_neg35
  linarith

#print axioms hpThetaCNV_exp_neg_pi_upper
#print axioms hpThetaCNV_secondDerivativeFactor_nonneg
#print axioms hpThetaCNV_secondDerivative_firstTerm_ge_neg35
#print axioms hpThetaCNV_secondDerivative_tailTerm_nonneg
#print axioms hpThetaPhi_secondDeriv_zero_ge_neg35
end HodgeProofHP
