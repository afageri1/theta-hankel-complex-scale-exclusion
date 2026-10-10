#!/usr/bin/env bash
set -euo pipefail

cat > HodgeProofHP/Stage3DeficiencyDomainBoundary.lean <<'LEAN'
import HodgeProofHP.Stage3ClosureNoNonrealEigen

/-!
A nonreal eigenvector of the core adjoint is zero if its underlying
L² vector also belongs to the domain of the harmonic closure.
-/

namespace HodgeProofHP

theorem hpHarmonicAdjoint_nonreal_eigen_of_mem_closure
    (c : ℂ) (hc : (starRingEnd ℂ) c ≠ c)
    (f : HPHarmonicCoreOperator.adjoint.domain)
    (hf : HPHarmonicCoreOperator.adjoint.toFun f =
      c • (f : HPSpace))
    (hmem : (f : HPSpace) ∈ HPHarmonicClosure.domain) :
    (f : HPSpace) = 0 := by
  let g : HPHarmonicClosure.domain := ⟨(f : HPSpace), hmem⟩
  obtain ⟨z, hz, hA⟩ :=
    LinearPMap.exists_of_le hpHarmonicClosure_le_core_adjoint g
  have hz' : z = f := by
    apply Subtype.ext
    change (f : HPSpace) = (z : HPSpace) at hz
    exact hz.symm
  change HPHarmonicClosure.toFun g =
    HPHarmonicCoreOperator.adjoint.toFun z at hA
  rw [hz'] at hA
  have hg : HPHarmonicClosure.toFun g = c • (g : HPSpace) := by
    rw [hA, hf]
  exact hpHarmonicClosure_no_nonreal_eigen c hc g hg

#print axioms hpHarmonicAdjoint_nonreal_eigen_of_mem_closure

end HodgeProofHP
LEAN

lake env lean HodgeProofHP/Stage3DeficiencyDomainBoundary.lean
lake build HodgeProofHP.Stage3DeficiencyDomainBoundary
