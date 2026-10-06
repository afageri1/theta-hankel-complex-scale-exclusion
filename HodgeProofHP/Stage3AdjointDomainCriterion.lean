import HodgeProofHP.Stage3SelfAdjointApiAudit

/-!
Explicit adjoint-domain criteria for the harmonic core and its closure.
These criteria do not assert equality of the domains.
-/

namespace HodgeProofHP

theorem hpHarmonicCore_adjoint_mem_domain_iff (g : HPSpace) :
    g ∈ HPHarmonicCoreOperator.adjoint.domain ↔
      Continuous ⇑((innerₛₗ ℂ) g ∘ₗ
        HPHarmonicCoreOperator.toFun) := by
  exact LinearPMap.mem_adjoint_domain_iff
    HPHarmonicCoreOperator g

theorem hpHarmonicClosure_adjoint_mem_domain_iff (g : HPSpace) :
    g ∈ HPHarmonicClosure.adjoint.domain ↔
      Continuous ⇑((innerₛₗ ℂ) g ∘ₗ
        HPHarmonicClosure.toFun) := by
  exact LinearPMap.mem_adjoint_domain_iff
    HPHarmonicClosure g

#print axioms hpHarmonicCore_adjoint_mem_domain_iff
#print axioms hpHarmonicClosure_adjoint_mem_domain_iff

end HodgeProofHP
