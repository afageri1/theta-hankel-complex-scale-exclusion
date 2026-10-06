import HodgeProofHP.Stage3HermiteTotality
import HodgeProofHP.Stage3HermiteCoreEigen
import HodgeProofHP.Stage3DeficiencyRangeOrthogonality

/-!
Hermite totality rules out nonzero eigenvectors of the harmonic
core adjoint with nonreal eigenvalues.
-/

namespace HodgeProofHP

theorem hpHarmonicAdjoint_nonreal_eigen_eq_zero
    (c : ℂ)
    (hc : c.im ≠ 0)
    (f : HPHarmonicCoreOperator.adjoint.domain)
    (hf : HPHarmonicCoreOperator.adjoint.toFun f =
      c • (f : HPSpace)) :
    (f : HPSpace) = 0 := by
  apply hpHermiteL2_inner_eq_zero_imp_eq_zero
  intro n

  have hs :=
    hpHarmonicAdjoint_eigen_orthogonal_shifted_range
      c f hf (hpHermiteCoreVector n)

  rw [hpHermite_core_eigen] at hs
  change
    inner ℂ (f : HPSpace)
      ((2 * (n : ℂ) + 1) • hpHermiteL2 n -
        (starRingEnd ℂ) c • hpHermiteL2 n) = 0 at hs

  simp only [inner_sub_right, inner_smul_right] at hs

  have hcoeff :
      (2 * (n : ℂ) + 1 - (starRingEnd ℂ) c) ≠ 0 := by
    intro h
    have heq :
        2 * (n : ℂ) + 1 = (starRingEnd ℂ) c :=
      sub_eq_zero.mp h
    have him : (0 : ℝ) = -c.im := by
      simpa using congrArg Complex.im heq
    exact hc (neg_eq_zero.mp him.symm)

  have hprod :
      (2 * (n : ℂ) + 1 - (starRingEnd ℂ) c) *
        inner ℂ (f : HPSpace) (hpHermiteL2 n) = 0 := by
    rw [sub_mul]
    exact hs

  exact (mul_eq_zero.mp hprod).resolve_left hcoeff

#print axioms hpHarmonicAdjoint_nonreal_eigen_eq_zero

end HodgeProofHP
