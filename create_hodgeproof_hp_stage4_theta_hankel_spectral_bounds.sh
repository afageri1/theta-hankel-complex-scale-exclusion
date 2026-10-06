#!/usr/bin/env bash
set -euo pipefail

lake build HodgeProofHP.Stage4ThetaHankelSpectralOrthogonality

target="HodgeProofHP/Stage4ThetaHankelSpectralBounds.lean"

if [ -f "$target" ]; then
  cp -p "$target" "$target.before_update_$(date +%Y%m%d_%H%M%S)"
fi

cat > "$target" <<'LEAN'
import HodgeProofHP.Stage4ThetaHankelSpectralOrthogonality
import Mathlib.Analysis.Normed.Operator.Basic

/-!
Quantitative spectral bounds for S = A* A.
-/

namespace HodgeProofHP

theorem hpThetaHankelAdjointSquare_eigenvalue_re_le_opNorm_sq
    (ev : ℂ) (f : HPThetaHankelSpace)
    (hf : f ≠ 0)
    (heig : hpThetaHankelAdjointSquare f = ev • f) :
    ev.re ≤ ‖hpThetaHankelOperator‖ ^ 2 := by
  have hbound := hpThetaHankelOperator.le_opNorm f
  have hproduct :
      0 ≤ ‖hpThetaHankelOperator‖ * ‖f‖ :=
    mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hmul :=
    mul_le_mul hbound hbound
      (norm_nonneg (hpThetaHankelOperator f)) hproduct
  have hsquare :
      ‖hpThetaHankelOperator f‖ ^ 2 ≤
        (‖hpThetaHankelOperator‖ * ‖f‖) ^ 2 := by
    simpa only [pow_two] using hmul
  rw [mul_pow] at hsquare
  have hpositive : 0 < ‖f‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr hf)
  rw [hpThetaHankelAdjointSquare_eigenvalue_energy_quotient
    ev f hf heig]
  exact (div_le_iff₀ hpositive).2 hsquare

theorem hpThetaHankelAdjointSquare_spectrum_re_mem_Icc
    (ev : ℂ)
    (hspec : ev ∈ spectrum ℂ hpThetaHankelAdjointSquare) :
    ev.re ∈ Set.Icc 0 (‖hpThetaHankelOperator‖ ^ 2) := by
  have hnonneg :=
    (hpThetaHankelAdjointSquare_spectrum_real_nonneg ev hspec).2
  refine ⟨hnonneg, ?_⟩
  by_cases hev : ev = 0
  · subst ev
    simpa only [Complex.zero_re] using
      sq_nonneg ‖hpThetaHankelOperator‖
  · obtain ⟨f, hf, heig⟩ :=
      hpThetaHankelAdjointSquare_mem_spectrum_exists_eigenvector
        ev hev hspec
    exact hpThetaHankelAdjointSquare_eigenvalue_re_le_opNorm_sq
      ev f hf heig

#print axioms hpThetaHankelAdjointSquare_eigenvalue_re_le_opNorm_sq
#print axioms hpThetaHankelAdjointSquare_spectrum_re_mem_Icc

end HodgeProofHP
LEAN

lake env lean "$target"
lake build HodgeProofHP.Stage4ThetaHankelSpectralBounds

printf '%s\n' 'PASS: Stage4ThetaHankelSpectralBounds'
