import HodgeProofHP.Stage3ClosureSymmetric

/-!
The harmonic closure is formally symmetric and has no nonreal
eigenvalues on its own domain. This does not prove self-adjointness.
-/

namespace HodgeProofHP

theorem hpHarmonicClosure_isFormalAdjoint :
    HPHarmonicClosure.IsFormalAdjoint HPHarmonicClosure := by
  intro f g
  obtain ⟨z, hz, hA⟩ :=
    LinearPMap.exists_of_le hpHarmonicClosure_le_adjoint f
  change HPHarmonicClosure.toFun f =
    HPHarmonicClosure.adjoint.toFun z at hA
  have h :=
    (LinearPMap.adjoint_isFormalAdjoint
      hpHarmonicClosure_domain_dense) z g
  calc
    inner ℂ (HPHarmonicClosure.toFun f) (g : HPSpace) =
        inner ℂ (HPHarmonicClosure.adjoint.toFun z) (g : HPSpace) := by rw [hA]
    _ = inner ℂ (z : HPSpace) (HPHarmonicClosure.toFun g) := h
    _ = inner ℂ (f : HPSpace) (HPHarmonicClosure.toFun g) := by rw [hz]

theorem hpHarmonicClosure_no_nonreal_eigen
    (c : ℂ) (hc : (starRingEnd ℂ) c ≠ c)
    (f : HPHarmonicClosure.domain)
    (hf : HPHarmonicClosure.toFun f = c • (f : HPSpace)) :
    (f : HPSpace) = 0 := by
  have hsym := hpHarmonicClosure_isFormalAdjoint f f
  change inner ℂ (HPHarmonicClosure.toFun f) (f : HPSpace) =
    inner ℂ (f : HPSpace) (HPHarmonicClosure.toFun f) at hsym
  rw [hf] at hsym
  have hcoeff :
      (starRingEnd ℂ) c * inner ℂ (f : HPSpace) (f : HPSpace) =
        c * inner ℂ (f : HPSpace) (f : HPSpace) := by
    simpa only [inner_smul_left, inner_smul_right] using hsym
  have hprod :
      ((starRingEnd ℂ) c - c) * inner ℂ (f : HPSpace) (f : HPSpace) = 0 := by
    rw [sub_mul]
    exact sub_eq_zero.mpr hcoeff
  have hinner : inner ℂ (f : HPSpace) (f : HPSpace) = 0 :=
    (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hc)
  exact inner_self_eq_zero.mp hinner

#print axioms hpHarmonicClosure_isFormalAdjoint
#print axioms hpHarmonicClosure_no_nonreal_eigen

end HodgeProofHP
