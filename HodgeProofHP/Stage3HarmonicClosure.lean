import HodgeProofHP.Stage3AdjointInclusion

/-!
The harmonic core operator is closable and has a closed extension.
-/

namespace HodgeProofHP

theorem hpHarmonicCoreOperator_isClosable :
    HPHarmonicCoreOperator.IsClosable := by
  apply (LinearPMap.isClosable_iff_exists_closed_extension).2
  exact ⟨HPHarmonicCoreOperator.adjoint,
    LinearPMap.adjoint_isClosed hpHarmonicCoreOperator_domain_dense,
    hpHarmonicCoreOperator_le_adjoint⟩

/-- Closure of the harmonic oscillator initially defined on Schwartz functions. -/
noncomputable def HPHarmonicClosure : HPSpace →ₗ.[ℂ] HPSpace :=
  HPHarmonicCoreOperator.closure

theorem hpHarmonicClosure_isClosed :
    HPHarmonicClosure.IsClosed :=
  hpHarmonicCoreOperator_isClosable.closure_isClosed

theorem hpHarmonicCoreOperator_le_closure :
    HPHarmonicCoreOperator ≤ HPHarmonicClosure :=
  LinearPMap.le_closure HPHarmonicCoreOperator

#print axioms hpHarmonicCoreOperator_isClosable
#print axioms HPHarmonicClosure
#print axioms hpHarmonicClosure_isClosed
#print axioms hpHarmonicCoreOperator_le_closure

end HodgeProofHP
