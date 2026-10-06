import HodgeProofHP.Stage3SchwartzFoundation

/-! Stage 3.2: the kinetic term on Schwartz functions. -/

namespace HodgeProofHP

/-- The map f ↦ -f'' from complex Schwartz functions into HPSpace. -/
noncomputable def hpSchwartzKineticToL2 :
    SchwartzMap ℝ ℂ →L[ℂ] HPSpace :=
  -(hpSchwartzToL2.comp hpSchwartzSecondDeriv)

#check hpSchwartzKineticToL2
#print axioms hpSchwartzKineticToL2

end HodgeProofHP
