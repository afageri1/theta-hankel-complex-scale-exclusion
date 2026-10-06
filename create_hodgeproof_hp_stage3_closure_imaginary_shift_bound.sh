#!/usr/bin/env bash
set -euo pipefail

mkdir -p HodgeProofHP

cat > HodgeProofHP/Stage3ClosureImaginaryShiftBound.lean <<'LEAN'
import HodgeProofHP.Stage3ClosureSymmetric
import HodgeProofHP.Stage3HermiteShiftedRange
import Mathlib.Tactic.Linarith

/-!
Norm estimates for unit imaginary shifts of the symmetric
harmonic closure. Closedness of the shifted range is separate.
-/

namespace HodgeProofHP

theorem hpHarmonicClosure_inner_self_im_eq_zero
    (x : HPHarmonicClosure.domain) :
    (inner ℂ (HPHarmonicClosure.toFun x) (x : HPSpace)).im = 0 := by
  obtain ⟨z, hz, hA⟩ :=
    LinearPMap.exists_of_le hpHarmonicClosure_le_adjoint x
  change HPHarmonicClosure.toFun x =
    HPHarmonicClosure.adjoint.toFun z at hA
  have hform :=
    (LinearPMap.adjoint_isFormalAdjoint
      hpHarmonicClosure_domain_dense) z x
  change
    inner ℂ (HPHarmonicClosure.adjoint.toFun z) (x : HPSpace) =
      inner ℂ (z : HPSpace) (HPHarmonicClosure.toFun x) at hform
  rw [← hA, ← hz] at hform
  have him := congrArg Complex.im hform
  have hswap :=
    inner_im_symm (𝕜 := ℂ)
      (HPHarmonicClosure.toFun x) (x : HPSpace)
  change
    (inner ℂ (HPHarmonicClosure.toFun x) (x : HPSpace)).im =
      -(inner ℂ (x : HPSpace) (HPHarmonicClosure.toFun x)).im
    at hswap
  linarith

theorem hpHarmonicClosure_unitImaginaryShift_norm_sq
    (s : ℂ) (hsRe : s.re = 0) (hsNorm : ‖s‖ = 1)
    (x : HPHarmonicClosure.domain) :
    ‖HPHarmonicClosure.toFun x - s • (x : HPSpace)‖ ^ 2 =
      ‖HPHarmonicClosure.toFun x‖ ^ 2 + ‖(x : HPSpace)‖ ^ 2 := by
  have him := hpHarmonicClosure_inner_self_im_eq_zero x
  have hcross :
      (inner ℂ (HPHarmonicClosure.toFun x)
        (s • (x : HPSpace))).re = 0 := by
    rw [inner_smul_right]
    change
      s.re * (inner ℂ (HPHarmonicClosure.toFun x) (x : HPSpace)).re -
        s.im * (inner ℂ (HPHarmonicClosure.toFun x) (x : HPSpace)).im = 0
    rw [hsRe, him]
    simp
  have hnorm : ‖s • (x : HPSpace)‖ = ‖(x : HPSpace)‖ := by
    rw [norm_smul, hsNorm, one_mul]
  have hsq :=
    norm_sub_sq (𝕜 := ℂ)
      (HPHarmonicClosure.toFun x) (s • (x : HPSpace))
  change
    ‖HPHarmonicClosure.toFun x - s • (x : HPSpace)‖ ^ 2 =
      ‖HPHarmonicClosure.toFun x‖ ^ 2 -
        2 * (inner ℂ (HPHarmonicClosure.toFun x)
          (s • (x : HPSpace))).re +
        ‖s • (x : HPSpace)‖ ^ 2 at hsq
  rw [hcross, hnorm] at hsq
  simpa only [mul_zero, sub_zero] using hsq

theorem hpHarmonicClosure_norm_le_unitImaginaryShift
    (s : ℂ) (hsRe : s.re = 0) (hsNorm : ‖s‖ = 1)
    (x : HPHarmonicClosure.domain) :
    ‖(x : HPSpace)‖ ≤
      ‖HPHarmonicClosure.toFun x - s • (x : HPSpace)‖ := by
  have hsq :=
    hpHarmonicClosure_unitImaginaryShift_norm_sq s hsRe hsNorm x
  have hx := norm_nonneg (x : HPSpace)
  have hy :=
    norm_nonneg (HPHarmonicClosure.toFun x - s • (x : HPSpace))
  have hA := sq_nonneg ‖HPHarmonicClosure.toFun x‖
  nlinarith

theorem hpHarmonicClosure_image_norm_le_unitImaginaryShift
    (s : ℂ) (hsRe : s.re = 0) (hsNorm : ‖s‖ = 1)
    (x : HPHarmonicClosure.domain) :
    ‖HPHarmonicClosure.toFun x‖ ≤
      ‖HPHarmonicClosure.toFun x - s • (x : HPSpace)‖ := by
  have hsq :=
    hpHarmonicClosure_unitImaginaryShift_norm_sq s hsRe hsNorm x
  have hA := norm_nonneg (HPHarmonicClosure.toFun x)
  have hy :=
    norm_nonneg (HPHarmonicClosure.toFun x - s • (x : HPSpace))
  have hx := sq_nonneg ‖(x : HPSpace)‖
  nlinarith

theorem hpHarmonicClosure_norm_le_pos_I_shift
    (x : HPHarmonicClosure.domain) :
    ‖(x : HPSpace)‖ ≤
      ‖HPHarmonicClosure.toFun x - Complex.I • (x : HPSpace)‖ := by
  exact hpHarmonicClosure_norm_le_unitImaginaryShift
    Complex.I (by simp) (by simp) x

theorem hpHarmonicClosure_norm_le_neg_I_shift
    (x : HPHarmonicClosure.domain) :
    ‖(x : HPSpace)‖ ≤
      ‖HPHarmonicClosure.toFun x - (-Complex.I) • (x : HPSpace)‖ := by
  exact hpHarmonicClosure_norm_le_unitImaginaryShift
    (-Complex.I) (by simp) (by simp) x

#print axioms hpHarmonicClosure_inner_self_im_eq_zero
#print axioms hpHarmonicClosure_unitImaginaryShift_norm_sq
#print axioms hpHarmonicClosure_norm_le_unitImaginaryShift
#print axioms hpHarmonicClosure_image_norm_le_unitImaginaryShift
#print axioms hpHarmonicClosure_norm_le_pos_I_shift
#print axioms hpHarmonicClosure_norm_le_neg_I_shift

end HodgeProofHP
LEAN

lake env lean HodgeProofHP/Stage3ClosureImaginaryShiftBound.lean
lake build HodgeProofHP.Stage3ClosureImaginaryShiftBound
