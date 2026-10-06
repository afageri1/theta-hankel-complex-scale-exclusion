import HodgeProofHP.Stage3SchwartzQuadraticAction

/-!
Stage 3.5: the harmonic-oscillator expression on Schwartz space
and its image in HPSpace. No closed or self-adjoint realization
is asserted.
-/

namespace HodgeProofHP

/-- The image of complex Schwartz functions in HPSpace. -/
noncomputable def HPSchwartzDomain : Submodule ℂ HPSpace :=
  hpSchwartzToL2.toLinearMap.range

/-- The expression f ↦ -f'' + x²f, mapped from Schwartz space to L². -/
noncomputable def hpSchwartzHarmonicToL2 :
    SchwartzMap ℝ ℂ →L[ℂ] HPSpace :=
  hpSchwartzKineticToL2 + hpSchwartzQuadraticToL2

#check HPSchwartzDomain
#check hpSchwartzHarmonicToL2
#check SchwartzMap.injective_toLp
#check SchwartzMap.denseRange_toLpCLM
#print axioms hpSchwartzHarmonicToL2

end HodgeProofHP
