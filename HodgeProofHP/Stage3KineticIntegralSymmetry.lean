import HodgeProofHP.Stage3ConjugationDerivatives
import HodgeProofHP.Stage3SecondDerivativeIntegrationByParts

/-!
The second-derivative term is symmetric under integration on Schwartz functions.
-/

namespace HodgeProofHP

theorem hpSchwartz_secondDeriv_integral_symmetry
    (f g : SchwartzMap ℝ ℂ) :
    (∫ x : ℝ, star (f x) * (hpSchwartzSecondDeriv g) x) =
      (∫ x : ℝ, star ((hpSchwartzSecondDeriv f) x) * g x) := by
  have h :=
    hpSchwartz_second_deriv_integration_by_parts (hpSchwartzConj f) g
  rw [← hpSchwartzConj_secondDeriv f] at h
  simpa only [hpSchwartzConj_apply, starRingEnd_apply] using h

#print axioms hpSchwartz_secondDeriv_integral_symmetry

end HodgeProofHP
