import HodgeProofHP.Stage3HarmonicSelfAdjoint
import HodgeProofHP.Stage3HermiteNonzero
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
Hermite eigenvectors of the self-adjoint harmonic closure,
their nonvanishing, and orthogonality.
This file does not assert a correspondence with Riemann Xi.
-/

namespace HodgeProofHP

theorem hpHermiteL2_mem_closure_domain (n : ℕ) :
    hpHermiteL2 n ∈ HPHarmonicClosure.domain := by
  obtain ⟨x, hx, _⟩ :=
    LinearPMap.exists_of_le hpHarmonicCoreOperator_le_closure
      (hpHermiteCoreVector n)
  change hpHermiteL2 n = (x : HPSpace) at hx
  rw [hx]
  exact x.property

noncomputable def hpHermiteClosureVector (n : ℕ) :
    HPHarmonicClosure.domain :=
  ⟨hpHermiteL2 n, hpHermiteL2_mem_closure_domain n⟩

theorem hpHermite_closure_eigen (n : ℕ) :
    HPHarmonicClosure.toFun (hpHermiteClosureVector n) =
      (2 * (n : ℂ) + 1) • hpHermiteL2 n := by
  obtain ⟨x, hx, hA⟩ :=
    LinearPMap.exists_of_le hpHarmonicCoreOperator_le_closure
      (hpHermiteCoreVector n)
  change hpHermiteL2 n = (x : HPSpace) at hx
  change
    HPHarmonicCoreOperator.toFun (hpHermiteCoreVector n) =
      HPHarmonicClosure.toFun x at hA
  have heq : hpHermiteClosureVector n = x := by
    apply Subtype.ext
    exact hx
  rw [heq, ← hA]
  exact hpHermite_core_eigen n

theorem hpHermiteClosureVector_ne_zero (n : ℕ) :
    (hpHermiteClosureVector n : HPSpace) ≠ 0 :=
  hpHermiteL2_ne_zero n

theorem hpHermiteL2_orthogonal_of_ne
    (n m : ℕ) (hnm : n ≠ m) :
    inner ℂ (hpHermiteL2 n) (hpHermiteL2 m) = 0 := by
  have hformal :=
    LinearPMap.adjoint_isFormalAdjoint hpHarmonicClosure_domain_dense
  rw [hpHarmonicClosure_adjoint_eq_self] at hformal
  have h := hformal (hpHermiteClosureVector n) (hpHermiteClosureVector m)
  change
    inner ℂ (HPHarmonicClosure.toFun (hpHermiteClosureVector n))
      (hpHermiteL2 m) =
    inner ℂ (hpHermiteL2 n)
      (HPHarmonicClosure.toFun (hpHermiteClosureVector m)) at h
  rw [hpHermite_closure_eigen, hpHermite_closure_eigen,
    inner_smul_left, inner_smul_right] at h
  have hstar :
      (starRingEnd ℂ) (2 * (n : ℂ) + 1) =
        2 * (n : ℂ) + 1 := by
    apply Complex.ext
    · rfl
    · change
        -(2 * (n : ℂ) + 1).im =
          (2 * (n : ℂ) + 1).im
      norm_num [Complex.mul_im]
  rw [hstar] at h
  have hcoeff :
      (2 * (n : ℂ) + 1) - (2 * (m : ℂ) + 1) ≠ 0 := by
    intro hz
    have heq := sub_eq_zero.mp hz
    have hreal :
        2 * (n : ℝ) + 1 = 2 * (m : ℝ) + 1 := by
      simpa using congrArg Complex.re heq
    have hcast : (n : ℝ) = (m : ℝ) := by
      linarith
    have heqNat : n = m := by
      exact_mod_cast hcast
    exact hnm heqNat
  have hprod :
      ((2 * (n : ℂ) + 1) - (2 * (m : ℂ) + 1)) *
        inner ℂ (hpHermiteL2 n) (hpHermiteL2 m) = 0 := by
    rw [sub_mul]
    exact sub_eq_zero.mpr h
  exact (mul_eq_zero.mp hprod).resolve_left hcoeff

theorem hpHermite_closure_eigenvector_exists (n : ℕ) :
    ∃ x : HPHarmonicClosure.domain,
      (x : HPSpace) ≠ 0 ∧
      HPHarmonicClosure.toFun x =
        (2 * (n : ℂ) + 1) • (x : HPSpace) := by
  exact ⟨hpHermiteClosureVector n,
    hpHermiteClosureVector_ne_zero n,
    hpHermite_closure_eigen n⟩

#print axioms hpHermiteL2_mem_closure_domain
#print axioms hpHermite_closure_eigen
#print axioms hpHermiteClosureVector_ne_zero
#print axioms hpHermiteL2_orthogonal_of_ne
#print axioms hpHermite_closure_eigenvector_exists

end HodgeProofHP
