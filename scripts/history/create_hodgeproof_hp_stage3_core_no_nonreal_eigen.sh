#!/usr/bin/env bash
set -euo pipefail

cat > HodgeProofHP/Stage3CoreNoNonrealEigen.lean <<'LEAN'
import HodgeProofHP.Stage3AdjointDomainCriterion

/-!
A formally symmetric operator has no nonzero eigenvector in its
own domain with a nonreal eigenvalue. This does not determine the
deficiency spaces in the domain of its adjoint.
-/

namespace HodgeProofHP

theorem hpHarmonicCore_no_nonreal_eigen
    (c : ℂ)
    (hc : (starRingEnd ℂ) c ≠ c)
    (f : HPHarmonicCoreOperator.domain)
    (hf : HPHarmonicCoreOperator.toFun f =
      c • (f : HPSpace)) :
    (f : HPSpace) = 0 := by
  have hsym :
      inner ℂ (c • (f : HPSpace)) (f : HPSpace) =
        inner ℂ (f : HPSpace) (c • (f : HPSpace)) := by
    have hformal := hpHarmonicCoreOperator_isFormalAdjoint f f
    change
      inner ℂ (HPHarmonicCoreOperator.toFun f) (f : HPSpace) =
        inner ℂ (f : HPSpace) (HPHarmonicCoreOperator.toFun f) at hformal
    rw [hf] at hformal
    exact hformal
  have hcoeff :
      (starRingEnd ℂ) c *
          inner ℂ (f : HPSpace) (f : HPSpace) =
        c * inner ℂ (f : HPSpace) (f : HPSpace) := by
    simpa only [inner_smul_left, inner_smul_right] using hsym
  have hprod :
      ((starRingEnd ℂ) c - c) *
          inner ℂ (f : HPSpace) (f : HPSpace) = 0 := by
    rw [sub_mul]
    exact sub_eq_zero.mpr hcoeff
  have hinner :
      inner ℂ (f : HPSpace) (f : HPSpace) = 0 :=
    (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hc)
  exact inner_self_eq_zero.mp hinner

#print axioms hpHarmonicCore_no_nonreal_eigen

end HodgeProofHP
LEAN

lake env lean HodgeProofHP/Stage3CoreNoNonrealEigen.lean
lake build HodgeProofHP.Stage3CoreNoNonrealEigen
