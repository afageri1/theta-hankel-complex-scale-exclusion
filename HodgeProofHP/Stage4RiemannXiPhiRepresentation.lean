import HodgeProofHP.Stage4ThetaImproperCosineIBP

/-!
Representation of the critical Riemann xi function by the
theta differential kernel Phi = B'' - B/4.
Integrability and the integral identity follow from the proved
improper integration-by-parts formula.
-/

noncomputable section

open MeasureTheory

namespace HodgeProofHP

theorem hpRiemannThetaDifferentialKernel_cos_integrand_eq
    (z : ℂ) :
    (fun u : ℝ =>
      (hpRiemannThetaDifferentialKernel u : ℂ) *
        Complex.cos (z * (u : ℂ))) =
    (fun u : ℝ =>
      ((deriv (deriv hpRiemannThetaLogProfile) u : ℝ) : ℂ) *
          Complex.cos (z * (u : ℂ)) -
        (1 / 4 : ℂ) *
          ((hpRiemannThetaLogProfile u : ℂ) *
            Complex.cos (z * (u : ℂ)))) := by
  funext u
  unfold hpRiemannThetaDifferentialKernel
  push_cast
  ring

theorem hpRiemannThetaDifferentialKernel_cos_integrableOn
    (z : ℂ) :
    IntegrableOn
      (fun u : ℝ =>
        (hpRiemannThetaDifferentialKernel u : ℂ) *
          Complex.cos (z * (u : ℂ)))
      (Set.Ioi 0) volume := by
  rw [hpRiemannThetaDifferentialKernel_cos_integrand_eq z]
  exact
    (hpRiemannThetaLogProfile_secondDeriv_cos_integrableOn z).sub
      ((hpRiemannThetaLogProfile_cos_integrableOn z).const_mul
        (1 / 4 : ℂ))

theorem hpRiemannThetaDifferentialKernel_cos_integral_split
    (z : ℂ) :
    (∫ u : ℝ in Set.Ioi 0,
      (hpRiemannThetaDifferentialKernel u : ℂ) *
        Complex.cos (z * (u : ℂ))) =
      (∫ u : ℝ in Set.Ioi 0,
        ((deriv (deriv hpRiemannThetaLogProfile) u : ℝ) : ℂ) *
          Complex.cos (z * (u : ℂ))) -
        (1 / 4 : ℂ) *
          (∫ u : ℝ in Set.Ioi 0,
            (hpRiemannThetaLogProfile u : ℂ) *
              Complex.cos (z * (u : ℂ))) := by
  rw [hpRiemannThetaDifferentialKernel_cos_integrand_eq z]
  rw [integral_sub
    (hpRiemannThetaLogProfile_secondDeriv_cos_integrableOn z)
    ((hpRiemannThetaLogProfile_cos_integrableOn z).const_mul
      (1 / 4 : ℂ))]
  rw [integral_const_mul]

theorem hpRiemannXiCritical_eq_differentialKernel_cosine_integral
    (z : ℂ) :
    hpRiemannXiCritical z =
      ∫ u : ℝ in Set.Ioi 0,
        (hpRiemannThetaDifferentialKernel u : ℂ) *
          Complex.cos (z * (u : ℂ)) := by
  rw [hpRiemannXiCritical_eq_logProfile_cosine_integral z]
  rw [hpRiemannThetaDifferentialKernel_cos_integral_split z]
  rw [hpRiemannThetaLogProfile_secondDeriv_improper_cosine_ibp z]
  ring

#print axioms hpRiemannThetaDifferentialKernel_cos_integrand_eq
#print axioms hpRiemannThetaDifferentialKernel_cos_integrableOn
#print axioms hpRiemannThetaDifferentialKernel_cos_integral_split
#print axioms hpRiemannXiCritical_eq_differentialKernel_cosine_integral

end HodgeProofHP
