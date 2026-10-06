import HodgeProofHP.Stage3HermiteCoordinates
import Mathlib.Tactic.NormNum

/-!
# Diagonal action in Hermite coordinates
The closure acts on Hermite coefficients by multiplication by 2n+1.
-/

noncomputable section

namespace HodgeProofHP

def hpHermiteNormalizedClosureVector (n : ℕ) :
    HPHarmonicClosure.domain :=
  (‖hpHermiteL2 n‖ : ℂ)⁻¹ • hpHermiteClosureVector n

theorem hpHermiteNormalizedClosureVector_coe (n : ℕ) :
    (hpHermiteNormalizedClosureVector n : HPSpace) =
      hpHermiteNormalizedL2 n := rfl

theorem hpHermiteNormalized_closure_eigen (n : ℕ) :
    HPHarmonicClosure.toFun
      (hpHermiteNormalizedClosureVector n) =
        (2 * (n : ℂ) + 1) • hpHermiteNormalizedL2 n := by
  unfold hpHermiteNormalizedClosureVector hpHermiteNormalizedL2
  rw [map_smul, hpHermite_closure_eigen]
  simp only [smul_smul]
  rw [mul_comm]

theorem hpHermiteEigenvalue_star (n : ℕ) :
    (starRingEnd ℂ) (2 * (n : ℂ) + 1) =
      2 * (n : ℂ) + 1 := by
  apply Complex.ext
  · rfl
  · change -(2 * (n : ℂ) + 1).im =
      (2 * (n : ℂ) + 1).im
    norm_num [Complex.mul_im]

theorem hpHermiteCoefficient_closure_action
    (f : HPHarmonicClosure.domain) (n : ℕ) :
    hpHermiteCoefficient (HPHarmonicClosure.toFun f) n =
      (2 * (n : ℂ) + 1) *
        hpHermiteCoefficient (f : HPSpace) n := by
  have hformal :=
    LinearPMap.adjoint_isFormalAdjoint
      hpHarmonicClosure_domain_dense
  rw [hpHarmonicClosure_adjoint_eq_self] at hformal
  have h := hformal (hpHermiteNormalizedClosureVector n) f
  change
    inner ℂ
      (HPHarmonicClosure.toFun
        (hpHermiteNormalizedClosureVector n))
      (f : HPSpace) =
    inner ℂ
      (hpHermiteNormalizedClosureVector n : HPSpace)
      (HPHarmonicClosure.toFun f) at h
  rw [hpHermiteNormalized_closure_eigen,
    hpHermiteNormalizedClosureVector_coe,
    inner_smul_left, hpHermiteEigenvalue_star] at h
  exact h.symm

theorem hpHermiteCoordinateEquiv_closure_action
    (f : HPHarmonicClosure.domain) (n : ℕ) :
    hpHermiteCoordinateEquiv (HPHarmonicClosure.toFun f) n =
      (2 * (n : ℂ) + 1) *
        hpHermiteCoordinateEquiv (f : HPSpace) n := by
  rw [hpHermiteCoordinateEquiv_apply,
    hpHermiteCoordinateEquiv_apply]
  exact hpHermiteCoefficient_closure_action f n

theorem hpHermite_closure_action_hasSum
    (f : HPHarmonicClosure.domain) :
    HasSum
      (fun n : ℕ =>
        ((2 * (n : ℂ) + 1) *
          hpHermiteCoefficient (f : HPSpace) n) •
            hpHermiteNormalizedL2 n)
      (HPHarmonicClosure.toFun f) := by
  simpa only [hpHermiteCoefficient_closure_action]
    using hpHermite_hasSum (HPHarmonicClosure.toFun f)

theorem hpHermite_closure_action_reconstruction
    (f : HPHarmonicClosure.domain) :
    (∑' n : ℕ,
      ((2 * (n : ℂ) + 1) *
        hpHermiteCoefficient (f : HPSpace) n) •
          hpHermiteNormalizedL2 n) =
      HPHarmonicClosure.toFun f :=
  (hpHermite_closure_action_hasSum f).tsum_eq

end HodgeProofHP

#print axioms HodgeProofHP.hpHermiteNormalized_closure_eigen
#print axioms HodgeProofHP.hpHermiteEigenvalue_star
#print axioms HodgeProofHP.hpHermiteCoefficient_closure_action
#print axioms HodgeProofHP.hpHermiteCoordinateEquiv_closure_action
#print axioms HodgeProofHP.hpHermite_closure_action_hasSum
#print axioms HodgeProofHP.hpHermite_closure_action_reconstruction
