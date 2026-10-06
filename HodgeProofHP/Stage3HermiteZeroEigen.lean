import HodgeProofHP.Stage3HermiteEigenApiAudit

/-!
The zeroth Hermite candidate is the Gaussian ground state.
This is the base case of the proposed Hermite eigenvalue induction.
-/

namespace HodgeProofHP

theorem hpHermiteL2_zero_eq_ground :
    hpHermiteL2 0 = hpGaussianGroundL2 := by
  change (hpSchwartzCoreEquiv hpComplexGaussianSchwartz : HPSpace) =
    hpGaussianGroundL2
  rw [hpGaussianGroundL2_eq_schwartz]
  rfl

theorem hpHermite_zero_core_eigen :
    HPHarmonicCoreOperator.toFun (hpHermiteCoreVector 0) =
      hpHermiteL2 0 := by
  change HPHarmonicCoreOperator.toFun
    (hpSchwartzCoreEquiv hpComplexGaussianSchwartz) = hpHermiteL2 0
  rw [hpComplexGaussian_core_eigen_equation]
  exact hpHermiteL2_zero_eq_ground.symm

#print axioms hpHermiteL2_zero_eq_ground
#print axioms hpHermite_zero_core_eigen

end HodgeProofHP
