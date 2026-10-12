/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenAssumptionFrontier
import HodgeProofHP.Stage7ThetaJensenCubicFactorization

/-!
# Certified degrees through three and the remaining assumption

The cubic certificate extends the accepted unshifted degrees to zero through
three. The earlier higher-degree definition is preserved unchanged. A separate
proposition records the still-unproved requirement for every degree at least
four. The RH theorem below assumes this proposition; it does not prove it.
-/

noncomputable section
namespace HodgeProofHP

/-- Unproved: every unshifted degree at least four has only real zeros. -/
def hpThetaJensenDegreesFromFourRealZeros : Prop :=
  ∀ d : ℕ, 4 ≤ d → hpThetaJensenDegreeRealZeros d

theorem hpThetaJensen_degreeThree_realZeros : hpThetaJensenDegreeRealZeros 3 := by
  intro w hw
  exact hpThetaJensenCubic_all_complex_zeros_real w hw

theorem hpThetaJensen_degree_le_three_realZeros (d : ℕ) (hd : d ≤ 3) :
    hpThetaJensenDegreeRealZeros d := by
  by_cases hsmall : d ≤ 2
  · exact hpThetaJensen_degree_le_two_realZeros d hsmall
  · have heq : d = 3 := by omega
    subst d
    exact hpThetaJensen_degreeThree_realZeros

theorem hpThetaJensen_allDegreesRealZeros_iff_degreesFromFour :
    hpThetaJensenAllDegreesRealZeros ↔ hpThetaJensenDegreesFromFourRealZeros := by
  constructor
  · intro h d hd w hw
    exact h d w hw
  · intro h d w hw
    by_cases hd : d ≤ 3
    · exact hpThetaJensen_degree_le_three_realZeros d hd w hw
    · exact h d (by omega) w hw

/-- Conditional only: the degree-at-least-four hypothesis remains unproved. -/
theorem hpThetaJensen_RH_of_degreesFromFourRealZeros
    (h : hpThetaJensenDegreesFromFourRealZeros) : RiemannHypothesis :=
  hpThetaJensen_RH_of_allDegreesRealZeros
    (hpThetaJensen_allDegreesRealZeros_iff_degreesFromFour.mpr h)

#print axioms hpThetaJensen_degreeThree_realZeros
#print axioms hpThetaJensen_degree_le_three_realZeros
#print axioms hpThetaJensen_allDegreesRealZeros_iff_degreesFromFour
#print axioms hpThetaJensen_RH_of_degreesFromFourRealZeros

end HodgeProofHP
