import HodgeProofHP.Stage4ThetaTraceTermPositivity
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
Positivity of the actual theta differential series on the positive half-line,
and comparison with each individual term, including the first term.
-/

noncomputable section

namespace HodgeProofHP

theorem hpThetaTrace_parameter_ge_three (n : ℕ) :
    3 ≤ hpThetaGaussianParameter n := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hs : 1 ≤ ((n : ℝ) + 1) ^ 2 := by
    nlinarith [sq_nonneg (n : ℝ)]
  have hmul :
      Real.pi ≤ Real.pi * ((n : ℝ) + 1) ^ 2 := by
    simpa using
      mul_le_mul_of_nonneg_left hs (le_of_lt Real.pi_pos)
  unfold hpThetaGaussianParameter
  exact le_trans (le_of_lt Real.pi_gt_three) hmul

theorem hpThetaTrace_series_term_pos
    (n : ℕ) (u : ℝ) (hu : 0 ≤ u) :
    0 < hpThetaGaussianKernelTerm (hpThetaGaussianParameter n) u := by
  have hx : 1 ≤ Real.exp (2 * u) := by
    have h := Real.add_one_le_exp (2 * u)
    linarith
  have hpoly :=
    hpThetaTrace_polynomial_pos
      (hpThetaGaussianParameter n)
      (Real.exp (2 * u))
      (hpThetaTrace_parameter_ge_three n)
      hx
  unfold hpThetaGaussianKernelTerm hpThetaGaussianProfile
  exact mul_pos hpoly
    (mul_pos (by norm_num) (Real.exp_pos _))

theorem hpThetaPhi_series_term_le
    (n : ℕ) (u : ℝ) (hu : 0 ≤ u) :
    hpThetaGaussianKernelTerm (hpThetaGaussianParameter n) u ≤
      hpRiemannThetaDifferentialKernel u := by
  rw [hpRiemannThetaDifferentialKernel_eq_tsum]
  exact
    (hpRiemannThetaDifferentialKernel_series_summable u).le_tsum n
      (fun m _ => le_of_lt (hpThetaTrace_series_term_pos m u hu))

theorem hpThetaPhi_first_term_le
    (u : ℝ) (hu : 0 ≤ u) :
    hpThetaGaussianKernelTerm Real.pi u ≤
      hpRiemannThetaDifferentialKernel u := by
  simpa [hpThetaGaussianParameter] using
    hpThetaPhi_series_term_le 0 u hu

theorem hpThetaPhi_pos_on_nonnegative
    (u : ℝ) (hu : 0 ≤ u) :
    0 < hpRiemannThetaDifferentialKernel u := by
  exact lt_of_lt_of_le
    (hpThetaTrace_series_term_pos 0 u hu)
    (hpThetaPhi_series_term_le 0 u hu)

theorem hpThetaPhi_abs_eq_on_nonnegative
    (u : ℝ) (hu : 0 ≤ u) :
    |hpRiemannThetaDifferentialKernel u| =
      hpRiemannThetaDifferentialKernel u := by
  exact abs_of_nonneg
    (le_of_lt (hpThetaPhi_pos_on_nonnegative u hu))

#print axioms hpThetaTrace_parameter_ge_three
#print axioms hpThetaTrace_series_term_pos
#print axioms hpThetaPhi_series_term_le
#print axioms hpThetaPhi_first_term_le
#print axioms hpThetaPhi_pos_on_nonnegative
#print axioms hpThetaPhi_abs_eq_on_nonnegative

end HodgeProofHP
