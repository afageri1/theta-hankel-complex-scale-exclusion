import HodgeProofHP.Stage3HarmonicCoreProperties

/-! The harmonic oscillator restricted to the Schwartz domain. -/

namespace HodgeProofHP

noncomputable def hpSchwartzCoreEquiv :
    SchwartzMap ℝ ℂ ≃ₗ[ℂ] HPSchwartzDomain :=
  LinearEquiv.ofInjective
    hpSchwartzToL2.toLinearMap hpSchwartzToL2_injective

noncomputable def HPHarmonicCoreOperator :
    HPSpace →ₗ.[ℂ] HPSpace where
  domain := HPSchwartzDomain
  toFun :=
    hpSchwartzHarmonicToL2.toLinearMap.comp
      hpSchwartzCoreEquiv.symm.toLinearMap

theorem hpHarmonicCoreOperator_apply (f : SchwartzMap ℝ ℂ) :
    HPHarmonicCoreOperator.toFun (hpSchwartzCoreEquiv f) =
      hpSchwartzHarmonicToL2 f := by
  change hpSchwartzHarmonicToL2
    (hpSchwartzCoreEquiv.symm (hpSchwartzCoreEquiv f)) =
      hpSchwartzHarmonicToL2 f
  rw [LinearEquiv.symm_apply_apply]

#check HPHarmonicCoreOperator
#check hpHarmonicCoreOperator_apply
#print axioms HPHarmonicCoreOperator
#print axioms hpHarmonicCoreOperator_apply

end HodgeProofHP
