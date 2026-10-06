import HodgeProofHP.Stage3HermiteGraphApproximation
import HodgeProofHP.Stage3UnitImaginaryResolventIdentity
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# Finite Hermite approximations of the unit imaginary resolvent

The approximating maps have range in a finite Hermite span.
Convergence here is pointwise in the Hilbert-space norm.
-/

noncomputable section

namespace HodgeProofHP

open Filter
open scoped Topology

def hpHermiteFiniteSpan (N : ℕ) : Submodule ℂ HPSpace :=
  Submodule.span ℂ
    (hpHermiteNormalizedL2 '' (↑(Finset.range N) : Set ℕ))

def hpHermiteFiniteProjection (N : ℕ) :
    HPSpace →L[ℂ] HPSpace :=
  ∑ n ∈ Finset.range N,
    ((innerSL ℂ) (hpHermiteNormalizedL2 n)).smulRight
      (hpHermiteNormalizedL2 n)

theorem hpHermiteFiniteProjection_apply (N : ℕ) (v : HPSpace) :
    hpHermiteFiniteProjection N v = hpHermiteTruncation N v := by
  unfold hpHermiteFiniteProjection hpHermiteTruncation hpHermiteCoefficient
  rw [ContinuousLinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro n hn
  change
    ((innerSL ℂ) (hpHermiteNormalizedL2 n)) v •
        hpHermiteNormalizedL2 n =
      inner ℂ (hpHermiteNormalizedL2 n) v •
        hpHermiteNormalizedL2 n
  rw [innerSL_apply_apply]

theorem hpHermiteTruncation_mem_finiteSpan (N : ℕ) (v : HPSpace) :
    hpHermiteTruncation N v ∈ hpHermiteFiniteSpan N := by
  unfold hpHermiteTruncation
  apply Submodule.sum_mem
  intro n hn
  apply Submodule.smul_mem
  apply Submodule.subset_span
  exact ⟨n, hn, rfl⟩

theorem hpHermiteFiniteProjection_mem_finiteSpan
    (N : ℕ) (v : HPSpace) :
    hpHermiteFiniteProjection N v ∈ hpHermiteFiniteSpan N := by
  rw [hpHermiteFiniteProjection_apply]
  exact hpHermiteTruncation_mem_finiteSpan N v

theorem hpHermiteFiniteProjection_range_le (N : ℕ) :
    LinearMap.range (hpHermiteFiniteProjection N).toLinearMap ≤
      hpHermiteFiniteSpan N := by
  rintro w ⟨v, rfl⟩
  exact hpHermiteFiniteProjection_mem_finiteSpan N v

theorem hpHermiteFiniteProjection_tendsto (v : HPSpace) :
    Tendsto (fun N => hpHermiteFiniteProjection N v)
      atTop (𝓝 v) := by
  simpa only [hpHermiteFiniteProjection_apply] using
    hpHermiteTruncation_tendsto v

def hpHermiteFiniteResolventApproximation
    (c : ℂ) (hcIm : c.im ≠ 0) (hcRe : c.re = 0)
    (hcNorm : ‖c‖ = 1) (N : ℕ) :
    HPSpace →L[ℂ] HPSpace :=
  (hpHermiteFiniteProjection N).comp
    (hpHarmonicUnitImaginaryResolvent c hcIm hcRe hcNorm)

theorem hpHermiteFiniteResolventApproximation_apply
    (c : ℂ) (hcIm : c.im ≠ 0) (hcRe : c.re = 0)
    (hcNorm : ‖c‖ = 1) (N : ℕ) (v : HPSpace) :
    hpHermiteFiniteResolventApproximation c hcIm hcRe hcNorm N v =
      ∑ n ∈ Finset.range N,
        (hpHermiteCoefficient v n /
          ((2 * (n : ℂ) + 1) - (starRingEnd ℂ) c)) •
            hpHermiteNormalizedL2 n := by
  rw [hpHermiteFiniteResolventApproximation,
    ContinuousLinearMap.comp_apply,
    hpHermiteFiniteProjection_apply]
  simp only [hpHermiteTruncation,
    hpHermiteCoefficient_unitImaginaryResolvent]

theorem hpHermiteFiniteResolventApproximation_range_le
    (c : ℂ) (hcIm : c.im ≠ 0) (hcRe : c.re = 0)
    (hcNorm : ‖c‖ = 1) (N : ℕ) :
    LinearMap.range
        (hpHermiteFiniteResolventApproximation
          c hcIm hcRe hcNorm N).toLinearMap ≤
      hpHermiteFiniteSpan N := by
  rintro w ⟨v, rfl⟩
  change
    hpHermiteFiniteProjection N
        (hpHarmonicUnitImaginaryResolvent c hcIm hcRe hcNorm v) ∈
      hpHermiteFiniteSpan N
  exact hpHermiteFiniteProjection_mem_finiteSpan N
    (hpHarmonicUnitImaginaryResolvent c hcIm hcRe hcNorm v)

theorem hpHermiteFiniteResolventApproximation_tendsto
    (c : ℂ) (hcIm : c.im ≠ 0) (hcRe : c.re = 0)
    (hcNorm : ‖c‖ = 1) (v : HPSpace) :
    Tendsto
      (fun N =>
        hpHermiteFiniteResolventApproximation c hcIm hcRe hcNorm N v)
      atTop
      (𝓝 (hpHarmonicUnitImaginaryResolvent c hcIm hcRe hcNorm v)) := by
  simpa only [hpHermiteFiniteResolventApproximation,
    ContinuousLinearMap.comp_apply] using
    hpHermiteFiniteProjection_tendsto
      (hpHarmonicUnitImaginaryResolvent c hcIm hcRe hcNorm v)

end HodgeProofHP

#print axioms HodgeProofHP.hpHermiteFiniteProjection_apply
#print axioms HodgeProofHP.hpHermiteFiniteProjection_range_le
#print axioms HodgeProofHP.hpHermiteFiniteProjection_tendsto
#print axioms HodgeProofHP.hpHermiteFiniteResolventApproximation_apply
#print axioms HodgeProofHP.hpHermiteFiniteResolventApproximation_range_le
#print axioms HodgeProofHP.hpHermiteFiniteResolventApproximation_tendsto
