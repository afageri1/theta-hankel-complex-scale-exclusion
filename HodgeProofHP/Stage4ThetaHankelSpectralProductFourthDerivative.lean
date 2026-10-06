import HodgeProofHP.Stage4ThetaHankelFiniteSpectralFourthDerivative
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
Summability of squared spectral values and the fourth derivative
at zero of the infinite spectral product.
-/

namespace HodgeProofHP

open Filter
open scoped Topology

theorem hpThetaHankelSpectralValues_sq_summable :
    Summable (fun i : HPThetaHankelSpectralIndex => i.1 ^ 2) := by
  have hn :
      Summable (fun i : HPThetaHankelSpectralIndex => ‖i.1‖) :=
    hpThetaHankelSpectralValues_norm_summable
  let C : ℝ := ∑' i : HPThetaHankelSpectralIndex, ‖i.1‖
  have hbound (i : HPThetaHankelSpectralIndex) :
      ‖i.1‖ ≤ C := by
    exact hn.le_tsum i (fun j _ => norm_nonneg j.1)
  have hmajor :
      Summable (fun i : HPThetaHankelSpectralIndex => C * ‖i.1‖) :=
    hn.mul_left C
  apply hmajor.of_norm_bounded
  intro i
  calc
    ‖i.1 ^ 2‖ = ‖i.1‖ * ‖i.1‖ := by
      rw [norm_pow, pow_two]
    _ ≤ C * ‖i.1‖ :=
      mul_le_mul_of_nonneg_right (hbound i) (norm_nonneg i.1)

noncomputable def hpThetaHankelSpectralSquareSum : ℂ :=
  ∑' i : HPThetaHankelSpectralIndex, i.1 ^ 2

theorem hpThetaHankelSpectralValues_sq_hasSum :
    HasSum (fun i : HPThetaHankelSpectralIndex => i.1 ^ 2)
      hpThetaHankelSpectralSquareSum := by
  exact hpThetaHankelSpectralValues_sq_summable.hasSum

theorem hpThetaHankelFiniteSpectralProduct_fourthDeriv_zero_tendsto_formula :
    Tendsto
      (fun F : Finset HPThetaHankelSpectralIndex =>
        hpThetaIteratedComplexDeriv 4
          (hpThetaHankelFiniteSpectralProduct F) 0)
      atTop
      (𝓝 (12 * ((hpThetaFirstTraceEnergy : ℂ) ^ 2 -
        hpThetaHankelSpectralSquareSum))) := by
  have hs :
      Tendsto
        (fun F : Finset HPThetaHankelSpectralIndex => ∑ i ∈ F, i.1)
        atTop (𝓝 (hpThetaFirstTraceEnergy : ℂ)) :=
    hpThetaHankelSpectralValues_hasSum
  have hq :
      Tendsto
        (fun F : Finset HPThetaHankelSpectralIndex =>
          ∑ i ∈ F, i.1 ^ 2)
        atTop (𝓝 hpThetaHankelSpectralSquareSum) :=
    hpThetaHankelSpectralValues_sq_hasSum
  have hm :
      Tendsto
        (fun F : Finset HPThetaHankelSpectralIndex =>
          12 * ((∑ i ∈ F, i.1) ^ 2 - ∑ i ∈ F, i.1 ^ 2))
        atTop
        (𝓝 (12 * ((hpThetaFirstTraceEnergy : ℂ) ^ 2 -
          hpThetaHankelSpectralSquareSum))) := by
    simpa only [pow_two] using
      (tendsto_const_nhds.mul ((hs.mul hs).sub hq))
  simpa only [hpThetaHankelFiniteSpectralProduct_fourthDeriv_zero] using hm

theorem hpThetaHankelSpectralProduct_fourthDeriv_zero :
    hpThetaIteratedComplexDeriv 4 hpThetaHankelSpectralProduct 0 =
      12 * ((hpThetaFirstTraceEnergy : ℂ) ^ 2 -
        hpThetaHankelSpectralSquareSum) := by
  exact tendsto_nhds_unique
    hpThetaHankelFiniteSpectralProduct_fourthDeriv_zero_tendsto
    hpThetaHankelFiniteSpectralProduct_fourthDeriv_zero_tendsto_formula

theorem hpThetaHankelSpectralProduct_fourthCoefficient :
    hpThetaIteratedComplexDeriv 4 hpThetaHankelSpectralProduct 0 / 24 =
      ((hpThetaFirstTraceEnergy : ℂ) ^ 2 -
        hpThetaHankelSpectralSquareSum) / 2 := by
  rw [hpThetaHankelSpectralProduct_fourthDeriv_zero]
  ring

#print axioms hpThetaHankelSpectralValues_sq_summable
#print axioms hpThetaHankelSpectralValues_sq_hasSum
#print axioms hpThetaHankelFiniteSpectralProduct_fourthDeriv_zero_tendsto_formula
#print axioms hpThetaHankelSpectralProduct_fourthDeriv_zero
#print axioms hpThetaHankelSpectralProduct_fourthCoefficient

end HodgeProofHP
