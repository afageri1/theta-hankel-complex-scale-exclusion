import HodgeProofHP.Stage5ThetaJensenQuadraticFactorization
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic

/-!
# All complex roots of the degree-two, shift-zero Jensen polynomial are real

Map the proved real factorization to the complex numbers. Every complex
zero equals one of the two certified real roots. No assertion is made
for higher degrees or other shifts, or about the zeros of the xi function.
-/
noncomputable section
namespace HodgeProofHP

theorem hpThetaJensenQuadratic_zero_complex_factorization :
    (hpThetaJensenPolynomial 2 0).map Complex.ofRealHom =
      Polynomial.C (hpThetaJensenGamma 2 : ℂ) *
        (Polynomial.X - Polynomial.C (hpThetaJensenQuadraticRootPlus 0 : ℂ)) *
        (Polynomial.X - Polynomial.C (hpThetaJensenQuadraticRootMinus 0 : ℂ)) := by
  have h := congrArg (fun p : Polynomial ℝ => p.map Complex.ofRealHom)
    hpThetaJensenQuadratic_zero_factorization
  simpa only [Polynomial.map_mul, Polynomial.map_sub,
    Polynomial.map_C, Polynomial.map_X, Complex.ofRealHom_eq_coe] using h

theorem hpThetaJensenQuadratic_zero_complex_eval_eq_zero_iff (z : ℂ) :
    ((hpThetaJensenPolynomial 2 0).map Complex.ofRealHom).eval z = 0 ↔
      z = (hpThetaJensenQuadraticRootPlus 0 : ℂ) ∨
        z = (hpThetaJensenQuadraticRootMinus 0 : ℂ) := by
  have ha : (hpThetaJensenGamma 2 : ℂ) ≠ 0 := by
    exact_mod_cast hpThetaJensenGamma_two_ne_zero
  rw [hpThetaJensenQuadratic_zero_complex_factorization]
  simp [Polynomial.eval_mul, Polynomial.eval_sub,
    Polynomial.eval_C, Polynomial.eval_X, mul_eq_zero, ha, sub_eq_zero]

theorem hpThetaJensenQuadratic_zero_complex_root_im_zero (z : ℂ)
    (hz : ((hpThetaJensenPolynomial 2 0).map Complex.ofRealHom).eval z = 0) :
    z.im = 0 := by
  rcases (hpThetaJensenQuadratic_zero_complex_eval_eq_zero_iff z).mp hz with h | h
  · rw [h]
    simp
  · rw [h]
    simp

theorem hpThetaJensenQuadratic_zero_complex_root_is_real (z : ℂ)
    (hz : ((hpThetaJensenPolynomial 2 0).map Complex.ofRealHom).eval z = 0) :
    ∃ x : ℝ, z = (x : ℂ) := by
  rcases (hpThetaJensenQuadratic_zero_complex_eval_eq_zero_iff z).mp hz with h | h
  · exact ⟨hpThetaJensenQuadraticRootPlus 0, h⟩
  · exact ⟨hpThetaJensenQuadraticRootMinus 0, h⟩

#print axioms hpThetaJensenQuadratic_zero_complex_factorization
#print axioms hpThetaJensenQuadratic_zero_complex_eval_eq_zero_iff
#print axioms hpThetaJensenQuadratic_zero_complex_root_im_zero
#print axioms hpThetaJensenQuadratic_zero_complex_root_is_real
end HodgeProofHP
