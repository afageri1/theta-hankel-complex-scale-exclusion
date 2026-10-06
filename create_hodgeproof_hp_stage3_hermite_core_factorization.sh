#!/usr/bin/env bash
set -euo pipefail

cat > HodgeProofHP/Stage3HermiteCoreFactorization.lean <<'LEAN'
import HodgeProofHP.Stage3HermiteFactorizationAlgebra

/-!
The harmonic operator on the Schwartz core factors as
a† a + I, with the resulting Schwartz function mapped into HPSpace.
-/

namespace HodgeProofHP

theorem hpSchwartzHarmonicToL2_factorization
    (f : SchwartzMap ℝ ℂ) :
    hpSchwartzHarmonicToL2 f =
      hpSchwartzToL2
        (hpSchwartzCreation (hpSchwartzAnnihilation f) + f) := by
  rw [hpSchwartzCreation_annihilation_algebra]
  change
    -hpSchwartzToL2 (hpSchwartzSecondDeriv f) +
        hpSchwartzToL2 (hpSchwartzQuadraticMul f) =
      hpSchwartzToL2
        (hpSchwartzQuadraticMul f - hpSchwartzSecondDeriv f)
  rw [map_sub]
  abel

theorem hpHarmonicCoreOperator_factorization
    (f : SchwartzMap ℝ ℂ) :
    HPHarmonicCoreOperator.toFun (hpSchwartzCoreEquiv f) =
      hpSchwartzToL2
        (hpSchwartzCreation (hpSchwartzAnnihilation f) + f) := by
  rw [hpHarmonicCoreOperator_apply,
    hpSchwartzHarmonicToL2_factorization]

#print axioms hpSchwartzHarmonicToL2_factorization
#print axioms hpHarmonicCoreOperator_factorization

end HodgeProofHP
LEAN

lake env lean HodgeProofHP/Stage3HermiteCoreFactorization.lean
lake build HodgeProofHP.Stage3HermiteCoreFactorization
