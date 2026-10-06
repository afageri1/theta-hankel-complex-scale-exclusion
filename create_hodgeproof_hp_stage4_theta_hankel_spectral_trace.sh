#!/usr/bin/env bash
set -euo pipefail

lake build HodgeProofHP.Stage4ThetaHankelSpectralSummability

target="HodgeProofHP/Stage4ThetaHankelSpectralTrace.lean"

if [ -f "$target" ]; then
  cp -p "$target" "$target.before_update_$(date +%Y%m%d_%H%M%S)"
fi

cat > "$target" <<'LEAN'
import HodgeProofHP.Stage4ThetaHankelSpectralSummability
import Mathlib.Topology.Algebra.InfiniteSum.Module

/-!
Absolute summability of the spectral values of the theta Hankel
adjoint square, and their identification with the project's
Hilbert-basis trace. No Fredholm determinant is assumed.
-/

namespace HodgeProofHP

theorem hpThetaHankelSpectralValue_norm_eq_re
    (i : HPThetaHankelSpectralIndex) :
    ‖i.1‖ = i.1.re := by
  have hnonneg : 0 ≤ i.1.re :=
    (hpThetaHankelSpectralValue_real_nonneg i).2
  calc
    ‖i.1‖ = ‖(i.1.re : ℂ)‖ :=
      congrArg norm (hpThetaHankelSpectralValue_eq_cast_re i)
    _ = i.1.re := by
      simp [Real.norm_eq_abs, abs_of_nonneg hnonneg]

theorem hpThetaHankelSpectralValues_norm_hasSum :
    HasSum (fun i : HPThetaHankelSpectralIndex => ‖i.1‖)
      hpThetaFirstTraceEnergy := by
  have hfun :
      (fun i : HPThetaHankelSpectralIndex => ‖i.1‖) =
      (fun i : HPThetaHankelSpectralIndex => i.1.re) := by
    funext i
    exact hpThetaHankelSpectralValue_norm_eq_re i
  rw [hfun]
  exact hpThetaHankelSpectralValues_re_hasSum

theorem hpThetaHankelSpectralValues_norm_summable :
    Summable (fun i : HPThetaHankelSpectralIndex => ‖i.1‖) :=
  hpThetaHankelSpectralValues_norm_hasSum.summable

theorem hpThetaHankelSpectralValues_hasSum :
    HasSum (fun i : HPThetaHankelSpectralIndex => i.1)
      (hpThetaFirstTraceEnergy : ℂ) := by
  have hcast :=
    Complex.ofRealCLM.hasSum hpThetaHankelSpectralValues_re_hasSum
  have hfun :
      (fun i : HPThetaHankelSpectralIndex =>
        Complex.ofRealCLM i.1.re) =
      (fun i : HPThetaHankelSpectralIndex => i.1) := by
    funext i
    simpa only [Complex.ofRealCLM_apply] using
      (hpThetaHankelSpectralValue_eq_cast_re i).symm
  rw [hfun] at hcast
  simpa only [Complex.ofRealCLM_apply] using hcast

theorem hpThetaHankelSpectralValues_tsum :
    (∑' i : HPThetaHankelSpectralIndex, i.1) =
      (hpThetaFirstTraceEnergy : ℂ) :=
  hpThetaHankelSpectralValues_hasSum.tsum_eq

theorem hpThetaHankelSpectralBasis_diagonal_eq_value
    (i : HPThetaHankelSpectralIndex) :
    inner ℂ (hpThetaHankelSpectralBasis i)
      (hpThetaHankelAdjointSquare (hpThetaHankelSpectralBasis i)) =
      i.1 := by
  calc
    inner ℂ (hpThetaHankelSpectralBasis i)
        (hpThetaHankelAdjointSquare (hpThetaHankelSpectralBasis i)) =
        ((‖hpThetaHankelOperator
          (hpThetaHankelSpectralBasis i)‖ ^ 2 : ℝ) : ℂ) :=
      hpThetaHankelAdjointSquare_inner (hpThetaHankelSpectralBasis i)
    _ = i.1 :=
      (hpThetaHankelSpectralValue_eq_cast_energy i).symm

theorem hpThetaHankelSpectralBasisTrace_eq_energy :
    hpThetaHankelBasisTrace hpThetaHankelSpectralBasis
      hpThetaHankelAdjointSquare =
      (hpThetaFirstTraceEnergy : ℂ) := by
  have hdiag :=
    hpThetaHankelBasisTrace_adjointSquare_hasSum
      hpThetaHankelSpectralBasis
  have hfun :
      (fun i : HPThetaHankelSpectralIndex =>
        inner ℂ (hpThetaHankelSpectralBasis i)
          (hpThetaHankelAdjointSquare (hpThetaHankelSpectralBasis i))) =
      (fun i : HPThetaHankelSpectralIndex => i.1) := by
    funext i
    exact hpThetaHankelSpectralBasis_diagonal_eq_value i
  rw [hfun] at hdiag
  exact hdiag.unique hpThetaHankelSpectralValues_hasSum

#print axioms hpThetaHankelSpectralValue_norm_eq_re
#print axioms hpThetaHankelSpectralValues_norm_summable
#print axioms hpThetaHankelSpectralValues_hasSum
#print axioms hpThetaHankelSpectralValues_tsum
#print axioms hpThetaHankelSpectralBasis_diagonal_eq_value
#print axioms hpThetaHankelSpectralBasisTrace_eq_energy

end HodgeProofHP
LEAN

lake env lean "$target"
lake build HodgeProofHP.Stage4ThetaHankelSpectralTrace

printf '%s\n' 'PASS: Stage4ThetaHankelSpectralTrace'
