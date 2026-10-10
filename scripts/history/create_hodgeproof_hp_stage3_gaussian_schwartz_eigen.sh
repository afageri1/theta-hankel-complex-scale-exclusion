#!/usr/bin/env bash
set -euo pipefail

cat > HodgeProofHP/Stage3GaussianSchwartzEigen.lean <<'LEAN'
import HodgeProofHP.Stage3HermiteHarmonicCreation

/-!
Lift the established Gaussian eigen-equation from HPSpace
back to Schwartz space using injectivity of hpSchwartzToL2.
-/

namespace HodgeProofHP

theorem hpComplexGaussian_schwartz_eigen :
    hpSchwartzHarmonicAction hpComplexGaussianSchwartz =
      hpComplexGaussianSchwartz := by
  apply hpSchwartzToL2_injective
  rw [hpSchwartzHarmonicAction_toL2]
  calc
    hpSchwartzHarmonicToL2 hpComplexGaussianSchwartz =
        HPHarmonicCoreOperator.toFun
          (hpSchwartzCoreEquiv hpComplexGaussianSchwartz) :=
      (hpHarmonicCoreOperator_apply hpComplexGaussianSchwartz).symm
    _ = hpGaussianGroundL2 :=
      hpComplexGaussian_core_eigen_equation
    _ = hpSchwartzToL2 hpComplexGaussianSchwartz := by
      rw [hpGaussianGroundL2_eq_schwartz]

#print axioms hpComplexGaussian_schwartz_eigen

end HodgeProofHP
LEAN

lake env lean HodgeProofHP/Stage3GaussianSchwartzEigen.lean
lake build HodgeProofHP.Stage3GaussianSchwartzEigen
