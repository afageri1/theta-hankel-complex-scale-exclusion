import HodgeProofHP.Stage3HermiteAdjointNoNonrealEigen

/-!
The harmonic core adjoint has trivial deficiency spaces
at the eigenvalues I and -I.
-/

namespace HodgeProofHP

theorem hpHarmonicAdjoint_pos_I_eigen_eq_zero
    (f : HPHarmonicCoreOperator.adjoint.domain)
    (hf : HPHarmonicCoreOperator.adjoint.toFun f =
      Complex.I • (f : HPSpace)) :
    (f : HPSpace) = 0 := by
  exact hpHarmonicAdjoint_nonreal_eigen_eq_zero
    Complex.I (by simp) f hf

theorem hpHarmonicAdjoint_neg_I_eigen_eq_zero
    (f : HPHarmonicCoreOperator.adjoint.domain)
    (hf : HPHarmonicCoreOperator.adjoint.toFun f =
      (-Complex.I) • (f : HPSpace)) :
    (f : HPSpace) = 0 := by
  exact hpHarmonicAdjoint_nonreal_eigen_eq_zero
    (-Complex.I) (by simp) f hf

#print axioms hpHarmonicAdjoint_pos_I_eigen_eq_zero
#print axioms hpHarmonicAdjoint_neg_I_eigen_eq_zero

end HodgeProofHP
