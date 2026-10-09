import HodgeProofHP.Stage6ThetaPhiAllMomentsIntegrability
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic

/-!
# Domination for the real hyperbolic-cosine moment expansion

A single integrable exponential envelope bounds every finite partial sum.
The pointwise weighted series sums to cosh times the theta kernel.
Interchanging integration and the infinite series, and identifying the
result with the xi function, remain subsequent proof obligations.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace HodgeProofHP

/-- The first N terms of the even exponential series. -/
def hpThetaPhiCoshPartial (N : ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N, x ^ (2 * n) / (Nat.factorial (2 * n) : ℝ)

theorem hpThetaPhi_cosh_le_exp_abs (x : ℝ) :
    Real.cosh x ≤ Real.exp |x| := by
  rw [Real.cosh_eq]
  have h1 := Real.exp_le_exp.mpr (le_abs_self x)
  have h2 := Real.exp_le_exp.mpr (neg_le_abs x)
  linarith

theorem hpThetaPhi_coshPartial_nonneg (N : ℕ) (x : ℝ) :
    0 ≤ hpThetaPhiCoshPartial N x := by
  apply Finset.sum_nonneg
  intro n hn
  apply div_nonneg
  · rw [pow_mul]
    positivity
  · exact Nat.cast_nonneg _

theorem hpThetaPhi_coshPartial_norm_le (N : ℕ) (t u : ℝ)
    (hu : 0 ≤ u) :
    ‖hpThetaPhiCoshPartial N (t * u)‖ ≤ Real.exp (|t| * u) := by
  rw [Real.norm_eq_abs,
    abs_of_nonneg (hpThetaPhi_coshPartial_nonneg N (t * u))]
  have hsum : hpThetaPhiCoshPartial N (t * u) ≤ Real.cosh (t * u) := by
    apply sum_le_hasSum (Finset.range N) _ (Real.hasSum_cosh (t * u))
    intro n hn
    apply div_nonneg
    · rw [pow_mul]
      positivity
    · exact Nat.cast_nonneg _
  have hbound := hpThetaPhi_cosh_le_exp_abs (t * u)
  rw [abs_mul, abs_of_nonneg hu] at hbound
  exact hsum.trans hbound

theorem hpThetaPhi_coshEnvelope_integrableOn (t : ℝ) :
    IntegrableOn
      (fun u : ℝ => Real.exp (|t| * u) *
        |hpRiemannThetaDifferentialKernel u|)
      (Set.Ioi 0) volume := by
  have h := (hpThetaPhi_exp_weighted_integrableOn |t|).norm
  simpa only [IntegrableOn, Real.norm_eq_abs, abs_mul,
    abs_of_pos (Real.exp_pos _)] using h

theorem hpThetaPhi_coshPartial_integrableOn (N : ℕ) (t : ℝ) :
    IntegrableOn
      (fun u : ℝ => hpThetaPhiCoshPartial N (t * u) *
        hpRiemannThetaDifferentialKernel u)
      (Set.Ioi 0) volume := by
  have hkernel := hpRiemannThetaDifferentialKernel_continuous
  have hcont : Continuous
      (fun u : ℝ => hpThetaPhiCoshPartial N (t * u) *
        hpRiemannThetaDifferentialKernel u) := by
    unfold hpThetaPhiCoshPartial
    fun_prop
  apply (hpThetaPhi_coshEnvelope_integrableOn t).mono'
    hcont.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  rw [norm_mul, Real.norm_eq_abs (hpRiemannThetaDifferentialKernel u)]
  exact mul_le_mul_of_nonneg_right
    (hpThetaPhi_coshPartial_norm_le N t u (le_of_lt hu))
    (abs_nonneg _)

theorem hpThetaPhi_coshSeries_hasSum (t u : ℝ) :
    HasSum
      (fun n : ℕ =>
        ((t * u) ^ (2 * n) / (Nat.factorial (2 * n) : ℝ)) *
          hpRiemannThetaDifferentialKernel u)
      (Real.cosh (t * u) * hpRiemannThetaDifferentialKernel u) := by
  exact (Real.hasSum_cosh (t * u)).mul_right
    (hpRiemannThetaDifferentialKernel u)

#print axioms hpThetaPhi_cosh_le_exp_abs
#print axioms hpThetaPhi_coshPartial_nonneg
#print axioms hpThetaPhi_coshPartial_norm_le
#print axioms hpThetaPhi_coshEnvelope_integrableOn
#print axioms hpThetaPhi_coshPartial_integrableOn
#print axioms hpThetaPhi_coshSeries_hasSum

end HodgeProofHP
