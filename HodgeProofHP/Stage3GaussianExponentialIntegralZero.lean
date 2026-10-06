import HodgeProofHP.Stage3GaussianTaylorDomination
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Vanishing exponential integrals from Gaussian-weighted moments. -/

open MeasureTheory Filter
open scoped BigOperators Topology

namespace HodgeProofHP

theorem hpGaussianMomentTaylorTerm_hasSum
    (v : HPSpace) (z : ℂ) (x : ℝ) :
    HasSum
      (fun n => hpGaussianMomentTaylorTerm v z n x)
      (Complex.exp (z * (x : ℂ)) *
        hpGaussianWeightedL2Function v x) := by
  have hs :
      HasSum
        (fun n : ℕ => (z * (x : ℂ)) ^ n / (n.factorial : ℂ))
        (Complex.exp (z * (x : ℂ))) := by
    rw [Complex.exp_eq_exp_ℂ]
    exact NormedSpace.expSeries_div_hasSum_exp (z * (x : ℂ))
  have heq :
      (fun n => hpGaussianMomentTaylorTerm v z n x) =
        (fun n : ℕ =>
          ((z * (x : ℂ)) ^ n / (n.factorial : ℂ)) *
            hpGaussianWeightedL2Function v x) := by
    funext n
    simp only [hpGaussianMomentTaylorTerm, mul_pow, div_eq_mul_inv]
    ring
  rw [heq]
  exact hs.mul_right (hpGaussianWeightedL2Function v x)

theorem hpGaussianMomentTaylorSum_tendsto
    (v : HPSpace) (z : ℂ) (x : ℝ) :
    Tendsto
      (fun N : ℕ =>
        ∑ n ∈ Finset.range N, hpGaussianMomentTaylorTerm v z n x)
      atTop
      (𝓝 (Complex.exp (z * (x : ℂ)) *
        hpGaussianWeightedL2Function v x)) :=
  (hpGaussianMomentTaylorTerm_hasSum v z x).tendsto_sum_nat

theorem hpGaussianWeightedL2Function_exponential_integral_eq_zero
    (v : HPSpace) (hv : v ∈ hpHermiteL2Span.orthogonal)
    (z : ℂ) :
    (∫ x : ℝ,
      Complex.exp (z * (x : ℂ)) *
        hpGaussianWeightedL2Function v x) = 0 := by
  have hmeas :
      ∀ N : ℕ, AEStronglyMeasurable
        (fun x : ℝ =>
          ∑ n ∈ Finset.range N, hpGaussianMomentTaylorTerm v z n x)
        volume := by
    intro N
    exact
      (integrable_finset_sum (Finset.range N)
        (fun n _ => hpGaussianMomentTaylorTerm_integrable v z n)).aestronglyMeasurable
  have hbound :
      ∀ N : ℕ, ∀ᵐ x : ℝ ∂volume,
        ‖∑ n ∈ Finset.range N, hpGaussianMomentTaylorTerm v z n x‖ ≤
          Real.exp (‖z‖ * |x|) *
            ‖hpGaussianWeightedL2Function v x‖ := by
    intro N
    exact Eventually.of_forall
      (fun x => hpGaussianMomentTaylorSum_norm_le v z N x)
  have hlim :
      ∀ᵐ x : ℝ ∂volume,
        Tendsto
          (fun N : ℕ =>
            ∑ n ∈ Finset.range N, hpGaussianMomentTaylorTerm v z n x)
          atTop
          (𝓝 (Complex.exp (z * (x : ℂ)) *
            hpGaussianWeightedL2Function v x)) :=
    Eventually.of_forall (fun x => hpGaussianMomentTaylorSum_tendsto v z x)
  have ht :=
    tendsto_integral_of_dominated_convergence
      (fun x : ℝ =>
        Real.exp (‖z‖ * |x|) *
          ‖hpGaussianWeightedL2Function v x‖)
      hmeas
      (hpGaussianMomentTaylorSum_bound_integrable v z)
      hbound hlim
  have hzero :
      Tendsto
        (fun N : ℕ =>
          ∫ x : ℝ,
            ∑ n ∈ Finset.range N, hpGaussianMomentTaylorTerm v z n x)
        atTop (𝓝 (0 : ℂ)) := by
    have heq :
        (fun N : ℕ =>
          ∫ x : ℝ,
            ∑ n ∈ Finset.range N, hpGaussianMomentTaylorTerm v z n x) =
          (fun _ : ℕ => (0 : ℂ)) := by
      funext N
      exact hpGaussianMomentTaylorSum_integral_eq_zero v hv z N
    rw [heq]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique ht hzero

#print axioms hpGaussianMomentTaylorTerm_hasSum
#print axioms hpGaussianMomentTaylorSum_tendsto
#print axioms hpGaussianWeightedL2Function_exponential_integral_eq_zero

end HodgeProofHP
