import HodgeProofHP.Stage3HermiteClosureEigen

/-!
Exact enumeration of eigenvalues of the harmonic closure.
No assertion about the full spectrum or Riemann Xi is made.
-/

namespace HodgeProofHP

theorem hpHarmonicClosure_eigen_eq_zero_of_not_hermite
    (c : ℂ)
    (hc : ∀ n : ℕ, c ≠ 2 * (n : ℂ) + 1)
    (f : HPHarmonicClosure.domain)
    (hf : HPHarmonicClosure.toFun f = c • (f : HPSpace)) :
    (f : HPSpace) = 0 := by
  apply hpHermiteL2_inner_eq_zero_imp_eq_zero
  intro n
  have hformal :=
    LinearPMap.adjoint_isFormalAdjoint hpHarmonicClosure_domain_dense
  rw [hpHarmonicClosure_adjoint_eq_self] at hformal
  have h := hformal (hpHermiteClosureVector n) f
  change
    inner ℂ (HPHarmonicClosure.toFun (hpHermiteClosureVector n))
      (f : HPSpace) =
    inner ℂ (hpHermiteL2 n) (HPHarmonicClosure.toFun f) at h
  rw [hpHermite_closure_eigen, hf,
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
  have hcoeff : 2 * (n : ℂ) + 1 - c ≠ 0 := by
    intro hz
    exact hc n (sub_eq_zero.mp hz).symm
  have hprod :
      (2 * (n : ℂ) + 1 - c) *
        inner ℂ (hpHermiteL2 n) (f : HPSpace) = 0 := by
    rw [sub_mul]
    exact sub_eq_zero.mpr h
  have hinner :
      inner ℂ (hpHermiteL2 n) (f : HPSpace) = 0 :=
    (mul_eq_zero.mp hprod).resolve_left hcoeff
  exact inner_eq_zero_symm.mp hinner

theorem hpHarmonicClosure_eigenvalue_eq_hermite
    (c : ℂ)
    (f : HPHarmonicClosure.domain)
    (hf0 : (f : HPSpace) ≠ 0)
    (hf : HPHarmonicClosure.toFun f = c • (f : HPSpace)) :
    ∃ n : ℕ, c = 2 * (n : ℂ) + 1 := by
  classical
  by_contra h
  have hc : ∀ n : ℕ, c ≠ 2 * (n : ℂ) + 1 := by
    intro n hn
    exact h ⟨n, hn⟩
  exact hf0
    (hpHarmonicClosure_eigen_eq_zero_of_not_hermite c hc f hf)

theorem hpHarmonicClosure_eigenvalue_iff (c : ℂ) :
    (∃ f : HPHarmonicClosure.domain,
      (f : HPSpace) ≠ 0 ∧
      HPHarmonicClosure.toFun f = c • (f : HPSpace)) ↔
    ∃ n : ℕ, c = 2 * (n : ℂ) + 1 := by
  constructor
  · rintro ⟨f, hf0, hf⟩
    exact hpHarmonicClosure_eigenvalue_eq_hermite c f hf0 hf
  · rintro ⟨n, rfl⟩
    exact hpHermite_closure_eigenvector_exists n

#print axioms hpHarmonicClosure_eigen_eq_zero_of_not_hermite
#print axioms hpHarmonicClosure_eigenvalue_eq_hermite
#print axioms hpHarmonicClosure_eigenvalue_iff

end HodgeProofHP
