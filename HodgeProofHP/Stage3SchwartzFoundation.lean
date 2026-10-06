import HodgeProofHP.Stage3SchrodingerApiAudit

/-!
Stage 3.1: complex Schwartz functions in HPSpace and their
second derivative. No Schrödinger domain or operator is asserted.
-/

namespace HodgeProofHP

/-- The quadratic potential used for the harmonic-oscillator model. -/
def hpQuadraticPotential (x : ℝ) : ℝ := x ^ 2

/-- The canonical continuous complex-linear map from Schwartz space to HPSpace. -/
noncomputable def hpSchwartzToL2 :
    SchwartzMap ℝ ℂ →L[ℂ] HPSpace :=
  SchwartzMap.toLpCLM ℂ ℂ 2 MeasureTheory.volume

/-- Twice differentiating a Schwartz function remains in Schwartz space. -/
noncomputable def hpSchwartzSecondDeriv :
    SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ :=
  (SchwartzMap.derivCLM ℂ ℂ).comp
    (SchwartzMap.derivCLM ℂ ℂ)

#check hpQuadraticPotential
#check hpSchwartzToL2
#check hpSchwartzSecondDeriv
#print axioms hpSchwartzToL2
#print axioms hpSchwartzSecondDeriv

end HodgeProofHP
