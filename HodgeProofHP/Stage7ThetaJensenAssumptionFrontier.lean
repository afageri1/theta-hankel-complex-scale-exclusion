import HodgeProofHP.Stage7ThetaJensenCofinalCriterion
import HodgeProofHP.Stage5ThetaJensenQuadraticComplexRoots

/-!
# Known degrees and the remaining Jensen assumption

The unshifted degrees zero and one have only real zeros by elementary algebra.
Degree two reuses the certified Stage 5 complex-root theorem. Therefore the
all-degree real-zero proposition is equivalent to its restriction to d >= 3.
The higher-degree proposition is a definition, not a theorem. The RH conclusion
below requires it explicitly and does not establish it.
-/

noncomputable section
namespace HodgeProofHP

/-- Unproved: every unshifted degree at least three has only real zeros. -/
def hpThetaJensenHigherDegreesRealZeros : Prop :=
  ∀ d : ℕ, 3 ≤ d → hpThetaJensenDegreeRealZeros d

theorem hpThetaJensen_degreeZero_realZeros : hpThetaJensenDegreeRealZeros 0 := by
  intro w hw
  have hzero : (hpThetaJensenGamma 0 : ℂ) = 0 := by
    simpa [hpThetaJensenPolynomial_zero] using hw
  have hreal : hpThetaJensenGamma 0 = 0 := by exact_mod_cast hzero
  exact False.elim ((ne_of_gt hpThetaJensenGamma_zero_pos) hreal)

theorem hpThetaJensen_degreeOne_realZeros : hpThetaJensenDegreeRealZeros 1 := by
  intro w hw
  have hzero : (hpThetaJensenGamma 0 : ℂ) + (hpThetaJensenGamma 1 : ℂ) * w = 0 := by
    simpa [hpThetaJensenPolynomial_one] using hw
  have hre : hpThetaJensenGamma 0 + hpThetaJensenGamma 1 * w.re = 0 := by
    simpa using congrArg Complex.re hzero
  have him : hpThetaJensenGamma 1 * w.im = 0 := by
    simpa using congrArg Complex.im hzero
  rcases mul_eq_zero.mp him with hgamma | hwim
  · have hreal : hpThetaJensenGamma 0 = 0 := by simpa [hgamma] using hre
    exact False.elim ((ne_of_gt hpThetaJensenGamma_zero_pos) hreal)
  · exact hwim

theorem hpThetaJensen_degreeTwo_realZeros : hpThetaJensenDegreeRealZeros 2 := by
  intro w hw
  apply hpThetaJensenQuadratic_zero_complex_root_im_zero w
  simpa only [Polynomial.eval_map] using hw

theorem hpThetaJensen_degree_le_two_realZeros (d : ℕ) (hd : d ≤ 2) :
    hpThetaJensenDegreeRealZeros d := by
  interval_cases d
  · exact hpThetaJensen_degreeZero_realZeros
  · exact hpThetaJensen_degreeOne_realZeros
  · exact hpThetaJensen_degreeTwo_realZeros

theorem hpThetaJensen_allDegreesRealZeros_iff_higherDegrees :
    hpThetaJensenAllDegreesRealZeros ↔ hpThetaJensenHigherDegreesRealZeros := by
  constructor
  · intro h d hd w hw
    exact h d w hw
  · intro h d w hw
    by_cases hd : d ≤ 2
    · exact hpThetaJensen_degree_le_two_realZeros d hd w hw
    · exact h d (by omega) w hw

/-- Conditional only: higher-degree real zeros have not been proved. -/
theorem hpThetaJensen_RH_of_higherDegreesRealZeros
    (h : hpThetaJensenHigherDegreesRealZeros) : RiemannHypothesis :=
  hpThetaJensen_RH_of_allDegreesRealZeros
    (hpThetaJensen_allDegreesRealZeros_iff_higherDegrees.mpr h)

#print axioms hpThetaJensen_degreeZero_realZeros
#print axioms hpThetaJensen_degreeOne_realZeros
#print axioms hpThetaJensen_degreeTwo_realZeros
#print axioms hpThetaJensen_degree_le_two_realZeros
#print axioms hpThetaJensen_allDegreesRealZeros_iff_higherDegrees
#print axioms hpThetaJensen_RH_of_higherDegreesRealZeros

end HodgeProofHP
