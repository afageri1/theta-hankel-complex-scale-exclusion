#!/usr/bin/env bash
set -euo pipefail

cat > HodgeProofHP/Stage3GaussianClosureEigenvector.lean <<'LEAN'
import HodgeProofHP.Stage3GaussianNonzero
import HodgeProofHP.Stage3HarmonicClosure

/-!
The nonzero Gaussian eigenvector persists in the closure of the
harmonic core operator. Self-adjointness is not asserted.
-/

namespace HodgeProofHP

theorem hpGaussianGroundL2_closure_eigenvector :
    ∃ f : HPHarmonicClosure.domain,
      (f : HPSpace) = hpGaussianGroundL2 ∧
      (f : HPSpace) ≠ 0 ∧
      HPHarmonicClosure.toFun f = (f : HPSpace) := by
  obtain ⟨y, hy, haction⟩ :=
    LinearPMap.exists_of_le hpHarmonicCoreOperator_le_closure
      (⟨hpGaussianGroundL2,
        hpGaussianGroundL2_mem_harmonic_domain⟩ :
          HPHarmonicCoreOperator.domain)
  refine ⟨y, hy.symm, ?_, ?_⟩
  · rw [← hy]
    exact hpGaussianGroundL2_ne_zero
  · calc
      HPHarmonicClosure.toFun y =
          HPHarmonicCoreOperator.toFun
            (⟨hpGaussianGroundL2,
              hpGaussianGroundL2_mem_harmonic_domain⟩ :
                HPHarmonicCoreOperator.domain) := haction.symm
      _ = hpGaussianGroundL2 :=
        hpGaussianGroundL2_eigen_equation
      _ = (y : HPSpace) := hy

#print axioms hpGaussianGroundL2_closure_eigenvector

end HodgeProofHP
LEAN

lake env lean HodgeProofHP/Stage3GaussianClosureEigenvector.lean
lake build HodgeProofHP.Stage3GaussianClosureEigenvector
