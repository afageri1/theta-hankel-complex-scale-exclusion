#!/usr/bin/env bash
set -euo pipefail

cat > HodgeProofHP/Stage3GaussianL2EigenEquation.lean <<'LEAN'
import HodgeProofHP.Stage3GaussianCoreEigenEquation

/-!
The Gaussian L² vector satisfies the harmonic core operator equation.
Nonzeroness is a separate next step.
-/

namespace HodgeProofHP

theorem hpGaussianGroundL2_eigen_equation :
    HPHarmonicCoreOperator.toFun
      (⟨hpGaussianGroundL2,
        hpGaussianGroundL2_mem_harmonic_domain⟩ :
          HPHarmonicCoreOperator.domain) =
      hpGaussianGroundL2 := by
  have hinput :
      (⟨hpGaussianGroundL2,
        hpGaussianGroundL2_mem_harmonic_domain⟩ :
          HPHarmonicCoreOperator.domain) =
        (hpSchwartzCoreEquiv hpComplexGaussianSchwartz :
          HPHarmonicCoreOperator.domain) := by
    apply Subtype.ext
    change hpGaussianGroundL2 =
      hpSchwartzToL2 hpComplexGaussianSchwartz
    exact hpGaussianGroundL2_eq_schwartz
  rw [hinput]
  exact hpComplexGaussian_core_eigen_equation

#print axioms hpGaussianGroundL2_eigen_equation

end HodgeProofHP
LEAN

lake env lean HodgeProofHP/Stage3GaussianL2EigenEquation.lean
lake build HodgeProofHP.Stage3GaussianL2EigenEquation
