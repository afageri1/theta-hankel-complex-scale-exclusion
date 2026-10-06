import HodgeProofHP.Stage3HarmonicCoreOperator

/-! Domain and action of the harmonic oscillator on the Schwartz core. -/

namespace HodgeProofHP

theorem hpHarmonicCoreOperator_domain_eq :
    HPHarmonicCoreOperator.domain = HPSchwartzDomain := rfl

theorem hpHarmonicCoreOperator_domain_dense :
    Dense (HPHarmonicCoreOperator.domain : Set HPSpace) := by
  change Dense (HPSchwartzDomain : Set HPSpace)
  exact hpSchwartzDomain_dense

theorem hpHarmonicCoreOperator_apply_components
    (f : SchwartzMap ℝ ℂ) :
    HPHarmonicCoreOperator.toFun (hpSchwartzCoreEquiv f) =
      hpSchwartzKineticToL2 f + hpSchwartzQuadraticToL2 f := by
  rw [hpHarmonicCoreOperator_apply]
  rfl

#print axioms hpHarmonicCoreOperator_domain_eq
#print axioms hpHarmonicCoreOperator_domain_dense
#print axioms hpHarmonicCoreOperator_apply_components

end HodgeProofHP
