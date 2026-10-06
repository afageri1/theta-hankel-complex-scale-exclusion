#!/usr/bin/env bash
set -euo pipefail

lake build HodgeProofHP.Stage4ThetaHankelSpectralBasis

target="HodgeProofHP/Stage4ThetaHankelSpectralValues.lean"

if [ -f "$target" ]; then
  cp -p "$target" "$target.before_update_$(date +%Y%m%d_%H%M%S)"
fi

cat > "$target" <<'LEAN'
import HodgeProofHP.Stage4ThetaHankelSpectralBasis

/-!
Reality, positivity and energy identities for the spectral basis values.
Values are indexed with their eigenspace multiplicities.
-/

namespace HodgeProofHP

theorem hpThetaHankelSpectralBasis_norm
    (i : HPThetaHankelSpectralIndex) :
    ‖hpThetaHankelSpectralBasis i‖ = 1 :=
  hpThetaHankelSpectralBasis_orthonormal.norm_eq_one i

theorem hpThetaHankelSpectralBasis_ne_zero
    (i : HPThetaHankelSpectralIndex) :
    hpThetaHankelSpectralBasis i ≠ 0 := by
  intro hzero
  have hnorm := hpThetaHankelSpectralBasis_norm i
  rw [hzero, norm_zero] at hnorm
  exact zero_ne_one hnorm

theorem hpThetaHankelSpectralValue_real_nonneg
    (i : HPThetaHankelSpectralIndex) :
    i.1.im = 0 ∧ 0 ≤ i.1.re := by
  exact hpThetaHankelAdjointSquare_eigenvalue_real_nonneg
    i.1 (hpThetaHankelSpectralBasis i)
    (hpThetaHankelSpectralBasis_ne_zero i)
    (hpThetaHankelSpectralBasis_apply i)

theorem hpThetaHankelSpectralValue_eq_cast_re
    (i : HPThetaHankelSpectralIndex) :
    i.1 = (i.1.re : ℂ) := by
  have him := (hpThetaHankelSpectralValue_real_nonneg i).1
  apply Complex.ext
  · simp
  · simpa using him

theorem hpThetaHankelSpectralValue_re_eq_energy
    (i : HPThetaHankelSpectralIndex) :
    i.1.re =
      ‖hpThetaHankelOperator (hpThetaHankelSpectralBasis i)‖ ^ 2 := by
  have h :=
    hpThetaHankelAdjointSquare_eigenvalue_energy_quotient
      i.1 (hpThetaHankelSpectralBasis i)
      (hpThetaHankelSpectralBasis_ne_zero i)
      (hpThetaHankelSpectralBasis_apply i)
  simpa only [hpThetaHankelSpectralBasis_norm, one_pow, div_one]
    using h

theorem hpThetaHankelSpectralValue_eq_cast_energy
    (i : HPThetaHankelSpectralIndex) :
    i.1 =
      ((‖hpThetaHankelOperator
        (hpThetaHankelSpectralBasis i)‖ ^ 2 : ℝ) : ℂ) := by
  rw [hpThetaHankelSpectralValue_eq_cast_re,
    hpThetaHankelSpectralValue_re_eq_energy]

#print axioms hpThetaHankelSpectralBasis_norm
#print axioms hpThetaHankelSpectralBasis_ne_zero
#print axioms hpThetaHankelSpectralValue_real_nonneg
#print axioms hpThetaHankelSpectralValue_eq_cast_re
#print axioms hpThetaHankelSpectralValue_re_eq_energy
#print axioms hpThetaHankelSpectralValue_eq_cast_energy

end HodgeProofHP
LEAN

lake env lean "$target"
lake build HodgeProofHP.Stage4ThetaHankelSpectralValues

printf '%s\n' 'PASS: Stage4ThetaHankelSpectralValues'
