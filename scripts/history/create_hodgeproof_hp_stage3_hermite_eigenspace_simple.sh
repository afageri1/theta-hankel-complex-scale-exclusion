#!/usr/bin/env bash
set -euo pipefail

mkdir -p HodgeProofHP

cat > HodgeProofHP/Stage3HermiteEigenspaceSimple.lean <<'LEAN'
import HodgeProofHP.Stage3HermiteDiagonalAction
import Mathlib.Tactic

/-!
# Simplicity of Hermite eigenspaces
Every eigenvector with eigenvalue 2n+1 is a scalar multiple of
the corresponding normalized Hermite vector.
-/

noncomputable section

namespace HodgeProofHP

theorem hpHermiteEigenvalue_injective :
    Function.Injective (fun n : ℕ => 2 * (n : ℂ) + 1) := by
  intro n m h
  have hr := congrArg Complex.re h
  norm_num [Complex.mul_re] at hr
  exact hr

theorem hpHermiteCoefficient_eigen_off_diagonal
    (n m : ℕ) (hmn : m ≠ n)
    (f : HPHarmonicClosure.domain)
    (hf : HPHarmonicClosure.toFun f =
      (2 * (n : ℂ) + 1) • (f : HPSpace)) :
    hpHermiteCoefficient (f : HPSpace) m = 0 := by
  have h := hpHermiteCoefficient_closure_action f m
  rw [hf] at h
  simp only [hpHermiteCoefficient, inner_smul_right] at h
  have hprod :
      ((2 * (m : ℂ) + 1) - (2 * (n : ℂ) + 1)) *
        hpHermiteCoefficient (f : HPSpace) m = 0 := by
    rw [sub_mul]
    exact sub_eq_zero.mpr h.symm
  have hne :
      (2 * (m : ℂ) + 1) - (2 * (n : ℂ) + 1) ≠ 0 := by
    intro heq
    exact hmn (hpHermiteEigenvalue_injective
      (sub_eq_zero.mp heq))
  exact (mul_eq_zero.mp hprod).resolve_left hne

theorem hpHermite_eigenvector_eq_coefficient_smul
    (n : ℕ) (f : HPHarmonicClosure.domain)
    (hf : HPHarmonicClosure.toFun f =
      (2 * (n : ℂ) + 1) • (f : HPSpace)) :
    (f : HPSpace) =
      hpHermiteCoefficient (f : HPSpace) n •
        hpHermiteNormalizedL2 n := by
  apply hpHermite_coefficients_ext
  intro m
  have hinner :=
    (orthonormal_iff_ite.mp
      hpHermiteNormalizedL2_orthonormal) m n
  by_cases hmn : m = n
  · subst m
    have hself :
        inner ℂ (hpHermiteNormalizedL2 n)
          (hpHermiteNormalizedL2 n) = 1 := by
      simpa using hinner
    simp only [hpHermiteCoefficient, inner_smul_right,
      hself, mul_one]
  · have hzero :=
      hpHermiteCoefficient_eigen_off_diagonal n m hmn f hf
    have hoff :
        inner ℂ (hpHermiteNormalizedL2 m)
          (hpHermiteNormalizedL2 n) = 0 := by
      simpa [hmn] using hinner
    simpa only [hpHermiteCoefficient, inner_smul_right,
      hoff, mul_zero] using hzero

theorem hpHermite_eigenvector_exists_scalar
    (n : ℕ) (f : HPHarmonicClosure.domain)
    (hf : HPHarmonicClosure.toFun f =
      (2 * (n : ℂ) + 1) • (f : HPSpace)) :
    ∃ a : ℂ, (f : HPSpace) = a • hpHermiteNormalizedL2 n :=
  ⟨hpHermiteCoefficient (f : HPSpace) n,
    hpHermite_eigenvector_eq_coefficient_smul n f hf⟩

theorem hpHermite_eigenvector_coefficient_ne_zero
    (n : ℕ) (f : HPHarmonicClosure.domain)
    (hf0 : (f : HPSpace) ≠ 0)
    (hf : HPHarmonicClosure.toFun f =
      (2 * (n : ℂ) + 1) • (f : HPSpace)) :
    hpHermiteCoefficient (f : HPSpace) n ≠ 0 := by
  intro hzero
  apply hf0
  rw [hpHermite_eigenvector_eq_coefficient_smul n f hf,
    hzero, zero_smul]

end HodgeProofHP

#print axioms HodgeProofHP.hpHermiteEigenvalue_injective
#print axioms HodgeProofHP.hpHermiteCoefficient_eigen_off_diagonal
#print axioms HodgeProofHP.hpHermite_eigenvector_eq_coefficient_smul
#print axioms HodgeProofHP.hpHermite_eigenvector_exists_scalar
#print axioms HodgeProofHP.hpHermite_eigenvector_coefficient_ne_zero
LEAN

lake env lean HodgeProofHP/Stage3HermiteEigenspaceSimple.lean
lake build HodgeProofHP.Stage3HermiteEigenspaceSimple
