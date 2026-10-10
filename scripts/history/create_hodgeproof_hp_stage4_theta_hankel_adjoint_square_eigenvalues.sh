#!/usr/bin/env bash
set -euo pipefail

lake build HodgeProofHP.Stage4ThetaHankelAdjointSquareSelfAdjoint
lake build HodgeProofHP.Stage4ThetaHankelAdjointSquarePairing

target="HodgeProofHP/Stage4ThetaHankelAdjointSquareEigenvalues.lean"

if [ -f "$target" ]; then
  backup="$target.before_update_$(date +%Y%m%d_%H%M%S)"
  cp -p "$target" "$backup"
  printf 'BACKUP: %s\n' "$backup"
fi

cat > "$target" <<'LEAN'
import HodgeProofHP.Stage4ThetaHankelAdjointSquareSelfAdjoint
import HodgeProofHP.Stage4ThetaHankelAdjointSquarePairing

/-!
Reality and nonnegativity of eigenvalues of the theta Hankel
adjoint square. These statements do not assert any correspondence
with zeros of the Riemann Xi function.
-/

namespace HodgeProofHP

theorem hpThetaHankelAdjointSquare_eigenvalue_norm_sq_identity
    (ev : ℂ) (f : HPThetaHankelSpace)
    (heig : hpThetaHankelAdjointSquare f = ev • f) :
    ev * ((‖f‖ ^ 2 : ℝ) : ℂ) =
      ((‖hpThetaHankelOperator f‖ ^ 2 : ℝ) : ℂ) := by
  have h := hpThetaHankelAdjointSquare_inner f
  rw [heig, inner_smul_right, inner_self_eq_norm_sq_to_K] at h
  convert h using 1 <;> push_cast <;> rfl

theorem hpThetaHankelAdjointSquare_eigenvalue_im_eq_zero
    (ev : ℂ) (f : HPThetaHankelSpace)
    (hf : f ≠ 0)
    (heig : hpThetaHankelAdjointSquare f = ev • f) :
    ev.im = 0 := by
  have h :=
    hpThetaHankelAdjointSquare_eigenvalue_norm_sq_identity ev f heig
  have him := congrArg Complex.im h
  simp only [Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, add_zero] at him
  have hnorm : 0 < ‖f‖ := norm_pos_iff.mpr hf
  have hsq : 0 < ‖f‖ ^ 2 := sq_pos_of_pos hnorm
  nlinarith

theorem hpThetaHankelAdjointSquare_eigenvalue_re_nonneg
    (ev : ℂ) (f : HPThetaHankelSpace)
    (hf : f ≠ 0)
    (heig : hpThetaHankelAdjointSquare f = ev • f) :
    0 ≤ ev.re := by
  have h :=
    hpThetaHankelAdjointSquare_eigenvalue_norm_sq_identity ev f heig
  have hre := congrArg Complex.re h
  simp only [Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero] at hre
  have hnorm : 0 < ‖f‖ := norm_pos_iff.mpr hf
  have hsq : 0 < ‖f‖ ^ 2 := sq_pos_of_pos hnorm
  have hnonneg : 0 ≤ ‖hpThetaHankelOperator f‖ ^ 2 :=
    sq_nonneg _
  nlinarith

theorem hpThetaHankelAdjointSquare_eigenvalue_real_nonneg
    (ev : ℂ) (f : HPThetaHankelSpace)
    (hf : f ≠ 0)
    (heig : hpThetaHankelAdjointSquare f = ev • f) :
    ev.im = 0 ∧ 0 ≤ ev.re := by
  exact ⟨
    hpThetaHankelAdjointSquare_eigenvalue_im_eq_zero ev f hf heig,
    hpThetaHankelAdjointSquare_eigenvalue_re_nonneg ev f hf heig⟩

#print axioms hpThetaHankelAdjointSquare_eigenvalue_norm_sq_identity
#print axioms hpThetaHankelAdjointSquare_eigenvalue_im_eq_zero
#print axioms hpThetaHankelAdjointSquare_eigenvalue_re_nonneg
#print axioms hpThetaHankelAdjointSquare_eigenvalue_real_nonneg

end HodgeProofHP
LEAN

lake env lean "$target"
lake build HodgeProofHP.Stage4ThetaHankelAdjointSquareEigenvalues

printf '%s\n' 'PASS: Stage4ThetaHankelAdjointSquareEigenvalues'
