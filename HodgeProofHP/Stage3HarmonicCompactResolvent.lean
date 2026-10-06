import HodgeProofHP.Stage3HermiteResolventTailBound
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-!
# Compactness of the harmonic unit imaginary resolvent

The finite Hermite approximations converge in operator norm.
Their compactness therefore implies compactness of the full resolvent.
-/

noncomputable section

namespace HodgeProofHP

open Filter
open scoped Topology

theorem hpHermiteResolvent_tail_rate_tendsto_zero :
    Tendsto (fun N : ℕ => (2 * (N : ℝ) + 1)⁻¹)
      atTop (𝓝 0) := by
  have hnat :
      Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hden :
      Tendsto (fun N : ℕ => 2 * (N : ℝ) + 1) atTop atTop := by
    apply Filter.tendsto_atTop_mono
      (f := fun N : ℕ => (N : ℝ)) _ hnat
    intro N
    have hN : 0 ≤ (N : ℝ) := by positivity
    linarith
  exact tendsto_inv_atTop_zero.comp hden

theorem hpHermiteFiniteResolventApproximation_error_opNorm_tendsto_zero
    (c : ℂ) (hcIm : c.im ≠ 0) (hcRe : c.re = 0)
    (hcNorm : ‖c‖ = 1) :
    Tendsto
      (fun N =>
        ‖hpHarmonicUnitImaginaryResolvent c hcIm hcRe hcNorm -
          hpHermiteFiniteResolventApproximation c hcIm hcRe hcNorm N‖)
      atTop (𝓝 0) := by
  exact squeeze_zero
    (fun N => norm_nonneg _)
    (fun N =>
      hpHermiteFiniteResolventApproximation_error_opNorm_le
        c hcIm hcRe hcNorm N)
    hpHermiteResolvent_tail_rate_tendsto_zero

theorem hpHermiteFiniteResolventApproximation_opNorm_tendsto
    (c : ℂ) (hcIm : c.im ≠ 0) (hcRe : c.re = 0)
    (hcNorm : ‖c‖ = 1) :
    Tendsto
      (fun N =>
        hpHermiteFiniteResolventApproximation c hcIm hcRe hcNorm N)
      atTop
      (𝓝 (hpHarmonicUnitImaginaryResolvent c hcIm hcRe hcNorm)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have heq :
      (fun N =>
        ‖hpHermiteFiniteResolventApproximation c hcIm hcRe hcNorm N -
          hpHarmonicUnitImaginaryResolvent c hcIm hcRe hcNorm‖) =
      (fun N =>
        ‖hpHarmonicUnitImaginaryResolvent c hcIm hcRe hcNorm -
          hpHermiteFiniteResolventApproximation c hcIm hcRe hcNorm N‖) := by
    funext N
    exact norm_sub_rev _ _
  rw [heq]
  exact hpHermiteFiniteResolventApproximation_error_opNorm_tendsto_zero
    c hcIm hcRe hcNorm

theorem hpHarmonicUnitImaginaryResolvent_isCompact
    (c : ℂ) (hcIm : c.im ≠ 0) (hcRe : c.re = 0)
    (hcNorm : ‖c‖ = 1) :
    IsCompactOperator
      (hpHarmonicUnitImaginaryResolvent c hcIm hcRe hcNorm) := by
  exact hpHarmonicUnitImaginaryResolvent_isCompact_of_norm_approximation
    c hcIm hcRe hcNorm
    (hpHermiteFiniteResolventApproximation_opNorm_tendsto
      c hcIm hcRe hcNorm)

end HodgeProofHP

#print axioms HodgeProofHP.hpHermiteResolvent_tail_rate_tendsto_zero
#print axioms HodgeProofHP.hpHermiteFiniteResolventApproximation_error_opNorm_tendsto_zero
#print axioms HodgeProofHP.hpHermiteFiniteResolventApproximation_opNorm_tendsto
#print axioms HodgeProofHP.hpHarmonicUnitImaginaryResolvent_isCompact
