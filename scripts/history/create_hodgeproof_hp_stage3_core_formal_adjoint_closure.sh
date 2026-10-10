#!/usr/bin/env bash
set -euo pipefail

cat > HodgeProofHP/Stage3CoreFormalAdjointClosure.lean <<'LEAN'
import HodgeProofHP.Stage3CoreNoNonrealEigen

/-!
The harmonic core and its closure satisfy the formal adjoint identity.
This does not assert that the closure is self-adjoint.
-/

namespace HodgeProofHP

theorem hpHarmonicCore_formalAdjoint_closure :
    HPHarmonicCoreOperator.IsFormalAdjoint HPHarmonicClosure := by
  intro x y
  obtain ⟨z, hz, hA⟩ :=
    LinearPMap.exists_of_le hpHarmonicClosure_le_core_adjoint y
  have h :=
    (LinearPMap.adjoint_isFormalAdjoint
      hpHarmonicCoreOperator_domain_dense).symm x z
  calc
    inner ℂ (HPHarmonicCoreOperator.toFun x) (y : HPSpace) =
        inner ℂ (HPHarmonicCoreOperator.toFun x) (z : HPSpace) := by rw [hz]
    _ = inner ℂ (x : HPSpace) (HPHarmonicCoreOperator.adjoint.toFun z) := h
    _ = inner ℂ (x : HPSpace) (HPHarmonicClosure.toFun y) := by
      change HPHarmonicClosure.toFun y =
        HPHarmonicCoreOperator.adjoint.toFun z at hA
      rw [hA]

theorem hpHarmonicCore_le_closure_adjoint :
    HPHarmonicCoreOperator ≤ HPHarmonicClosure.adjoint :=
  LinearPMap.IsFormalAdjoint.le_adjoint
    hpHarmonicClosure_domain_dense
    hpHarmonicCore_formalAdjoint_closure.symm

#print axioms hpHarmonicCore_formalAdjoint_closure
#print axioms hpHarmonicCore_le_closure_adjoint

end HodgeProofHP
LEAN

lake env lean HodgeProofHP/Stage3CoreFormalAdjointClosure.lean
lake build HodgeProofHP.Stage3CoreFormalAdjointClosure
