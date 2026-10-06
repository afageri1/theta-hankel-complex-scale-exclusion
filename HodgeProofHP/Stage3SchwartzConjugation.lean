import HodgeProofHP.Stage3SecondDerivativeIntegrationByParts

/-! Complex conjugation preserves the real vector space of Schwartz maps. -/

namespace HodgeProofHP

noncomputable def hpSchwartzConj :
    SchwartzMap ℝ ℂ →L[ℝ] SchwartzMap ℝ ℂ :=
  SchwartzMap.postcompCLM Complex.conjCLE.toContinuousLinearMap

theorem hpSchwartzConj_apply (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    (hpSchwartzConj f) x = (starRingEnd ℂ) (f x) := by
  simp [hpSchwartzConj]

#check hpSchwartzConj
#print axioms hpSchwartzConj_apply

end HodgeProofHP
