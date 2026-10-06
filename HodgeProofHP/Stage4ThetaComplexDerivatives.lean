import HodgeProofHP.Stage4SecondOrderIntegrationByParts
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
Complex-valued derivative interfaces for the theta profile and
the trigonometric factors used in finite-interval integration by parts.
-/

namespace HodgeProofHP

theorem hpThetaComplexProfile_hasDerivAt (u : ℝ) :
    HasDerivAt
      (fun x : ℝ => (hpRiemannThetaLogProfile x : ℂ))
      ((deriv hpRiemannThetaLogProfile u : ℝ) : ℂ) u := by
  have h := hpRiemannThetaLogProfile_hasDerivAt u
  rw [← hpRiemannThetaLogProfile_deriv_eq_tsum u] at h
  exact h.ofReal_comp

theorem hpThetaComplexProfileFirst_hasDerivAt (u : ℝ) :
    HasDerivAt
      (fun x : ℝ => ((deriv hpRiemannThetaLogProfile x : ℝ) : ℂ))
      ((deriv (deriv hpRiemannThetaLogProfile) u : ℝ) : ℂ) u := by
  have h := hpRiemannThetaLogProfile_first_hasDerivAt u
  have hval :
      deriv (deriv hpRiemannThetaLogProfile) u =
        ∑' n : ℕ, hpThetaGaussianSecondTerm n u :=
    congrFun hpRiemannThetaLogProfile_secondDeriv_function u
  rw [← hval] at h
  exact h.ofReal_comp

theorem hpThetaComplexCos_hasDerivAt (z : ℂ) (u : ℝ) :
    HasDerivAt
      (fun x : ℝ => Complex.cos (z * (x : ℂ)))
      (-z * Complex.sin (z * (u : ℂ))) u := by
  have harg :
      HasDerivAt (fun x : ℝ => z * (x : ℂ)) z u := by
    simpa using
      ((hasDerivAt_id u).ofReal_comp).const_mul z
  convert (Complex.hasDerivAt_cos (z * (u : ℂ))).comp u harg using 1 <;>
    first | rfl | ring

theorem hpThetaComplexSin_hasDerivAt (z : ℂ) (u : ℝ) :
    HasDerivAt
      (fun x : ℝ => Complex.sin (z * (x : ℂ)))
      (z * Complex.cos (z * (u : ℂ))) u := by
  have harg :
      HasDerivAt (fun x : ℝ => z * (x : ℂ)) z u := by
    simpa using
      ((hasDerivAt_id u).ofReal_comp).const_mul z
  simpa only [Function.comp_def, mul_comm] using
    (Complex.hasDerivAt_sin (z * (u : ℂ))).comp u harg

theorem hpThetaComplexCosFirst_hasDerivAt (z : ℂ) (u : ℝ) :
    HasDerivAt
      (fun x : ℝ => -z * Complex.sin (z * (x : ℂ)))
      (-(z ^ 2) * Complex.cos (z * (u : ℂ))) u := by
  convert (hpThetaComplexSin_hasDerivAt z u).const_mul (-z) using 1 <;>
    ring

#print axioms hpThetaComplexProfile_hasDerivAt
#print axioms hpThetaComplexProfileFirst_hasDerivAt
#print axioms hpThetaComplexCos_hasDerivAt
#print axioms hpThetaComplexSin_hasDerivAt
#print axioms hpThetaComplexCosFirst_hasDerivAt

end HodgeProofHP
