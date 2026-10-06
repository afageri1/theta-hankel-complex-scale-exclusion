#!/usr/bin/env bash
set -euo pipefail

mkdir -p HodgeProofHP

cat > HodgeProofHP/Stage4ThetaTrigonometricIntegrability.lean <<'LEAN'
import HodgeProofHP.Stage4ThetaProfileWeightedIntegrability

/-!
Integrability of theta trigonometric products for complex frequencies.
-/

noncomputable section

namespace HodgeProofHP

open Filter MeasureTheory
open scoped Topology

theorem hpTheta_mul_complex_exp_integrableOn
    (f : ℝ → ℝ) (hcont : Continuous f)
    (hf : ∀ c : ℝ,
      IntegrableOn (fun u : ℝ => Real.exp (c * u) * f u)
        (Set.Ioi 0) volume)
    (a : ℂ) :
    IntegrableOn
      (fun u : ℝ => (f u : ℂ) * Complex.exp (a * (u : ℂ)))
      (Set.Ioi 0) volume := by
  have hcomplex :
      Continuous
        (fun u : ℝ => (f u : ℂ) * Complex.exp (a * (u : ℂ))) :=
    (Complex.continuous_ofReal.comp hcont).mul
      ((continuous_const.mul Complex.continuous_ofReal).cexp)
  have hweight :
      Integrable
        (fun u : ℝ => Real.exp (a.re * u) * f u)
        (volume.restrict (Set.Ioi 0)) :=
    hf a.re
  apply hweight.mono hcomplex.aestronglyMeasurable
  filter_upwards [] with u
  have hnorm :
      ‖(f u : ℂ) * Complex.exp (a * (u : ℂ))‖ =
        ‖Real.exp (a.re * u) * f u‖ := by
    simp [norm_mul, Complex.norm_exp, Real.norm_eq_abs, mul_comm]
  exact hnorm.le

theorem hpTheta_mul_complex_cos_integrableOn
    (f : ℝ → ℝ) (hcont : Continuous f)
    (hf : ∀ c : ℝ,
      IntegrableOn (fun u : ℝ => Real.exp (c * u) * f u)
        (Set.Ioi 0) volume)
    (t : ℂ) :
    IntegrableOn
      (fun u : ℝ => (f u : ℂ) * Complex.cos (t * (u : ℂ)))
      (Set.Ioi 0) volume := by
  have hplus := hpTheta_mul_complex_exp_integrableOn
    f hcont hf (t * Complex.I)
  have hminus := hpTheta_mul_complex_exp_integrableOn
    f hcont hf (-t * Complex.I)
  have hsum :
      IntegrableOn
        (fun u : ℝ =>
          ((f u : ℂ) * Complex.exp ((t * Complex.I) * (u : ℂ)) +
            (f u : ℂ) * Complex.exp ((-t * Complex.I) * (u : ℂ))) *
              (2 : ℂ)⁻¹)
        (Set.Ioi 0) volume :=
    (hplus.add hminus).mul_const ((2 : ℂ)⁻¹)
  have hfun :
      (fun u : ℝ => (f u : ℂ) * Complex.cos (t * (u : ℂ))) =
      (fun u : ℝ =>
        ((f u : ℂ) * Complex.exp ((t * Complex.I) * (u : ℂ)) +
          (f u : ℂ) * Complex.exp ((-t * Complex.I) * (u : ℂ))) *
            (2 : ℂ)⁻¹) := by
    funext u
    have hpos :
        (t * (u : ℂ)) * Complex.I =
          (t * Complex.I) * (u : ℂ) := by ring
    have hneg :
        -(t * (u : ℂ)) * Complex.I =
          (-t * Complex.I) * (u : ℂ) := by ring
    rw [Complex.cos, hpos, hneg, div_eq_mul_inv]
    ring
  rw [hfun]
  exact hsum

theorem hpTheta_mul_complex_sin_integrableOn
    (f : ℝ → ℝ) (hcont : Continuous f)
    (hf : ∀ c : ℝ,
      IntegrableOn (fun u : ℝ => Real.exp (c * u) * f u)
        (Set.Ioi 0) volume)
    (t : ℂ) :
    IntegrableOn
      (fun u : ℝ => (f u : ℂ) * Complex.sin (t * (u : ℂ)))
      (Set.Ioi 0) volume := by
  have hplus := hpTheta_mul_complex_exp_integrableOn
    f hcont hf (t * Complex.I)
  have hminus := hpTheta_mul_complex_exp_integrableOn
    f hcont hf (-t * Complex.I)
  have hdiff :
      IntegrableOn
        (fun u : ℝ =>
          (((f u : ℂ) * Complex.exp ((-t * Complex.I) * (u : ℂ)) -
            (f u : ℂ) * Complex.exp ((t * Complex.I) * (u : ℂ))) *
              Complex.I) * (2 : ℂ)⁻¹)
        (Set.Ioi 0) volume :=
    ((hminus.sub hplus).mul_const Complex.I).mul_const ((2 : ℂ)⁻¹)
  have hfun :
      (fun u : ℝ => (f u : ℂ) * Complex.sin (t * (u : ℂ))) =
      (fun u : ℝ =>
        (((f u : ℂ) * Complex.exp ((-t * Complex.I) * (u : ℂ)) -
          (f u : ℂ) * Complex.exp ((t * Complex.I) * (u : ℂ))) *
            Complex.I) * (2 : ℂ)⁻¹) := by
    funext u
    have hpos :
        (t * (u : ℂ)) * Complex.I =
          (t * Complex.I) * (u : ℂ) := by ring
    have hneg :
        -(t * (u : ℂ)) * Complex.I =
          (-t * Complex.I) * (u : ℂ) := by ring
    rw [Complex.sin, hpos, hneg, div_eq_mul_inv]
    ring
  rw [hfun]
  exact hdiff

theorem hpRiemannThetaLogProfile_cos_integrableOn
    (t : ℂ) :
    IntegrableOn
      (fun u : ℝ =>
        (hpRiemannThetaLogProfile u : ℂ) *
          Complex.cos (t * (u : ℂ)))
      (Set.Ioi 0) volume := by
  exact hpTheta_mul_complex_cos_integrableOn
    hpRiemannThetaLogProfile
    hpRiemannThetaLogProfile_continuous
    hpRiemannThetaLogProfile_exp_weighted_integrableOn t

theorem hpRiemannThetaLogProfile_sin_integrableOn
    (t : ℂ) :
    IntegrableOn
      (fun u : ℝ =>
        (hpRiemannThetaLogProfile u : ℂ) *
          Complex.sin (t * (u : ℂ)))
      (Set.Ioi 0) volume := by
  exact hpTheta_mul_complex_sin_integrableOn
    hpRiemannThetaLogProfile
    hpRiemannThetaLogProfile_continuous
    hpRiemannThetaLogProfile_exp_weighted_integrableOn t

theorem hpRiemannThetaLogProfile_deriv_cos_integrableOn
    (t : ℂ) :
    IntegrableOn
      (fun u : ℝ =>
        ((deriv hpRiemannThetaLogProfile u : ℝ) : ℂ) *
          Complex.cos (t * (u : ℂ)))
      (Set.Ioi 0) volume := by
  exact hpTheta_mul_complex_cos_integrableOn
    (deriv hpRiemannThetaLogProfile)
    hpRiemannThetaLogProfile_deriv_continuous
    hpRiemannThetaLogProfile_deriv_exp_weighted_integrableOn t

theorem hpRiemannThetaLogProfile_deriv_sin_integrableOn
    (t : ℂ) :
    IntegrableOn
      (fun u : ℝ =>
        ((deriv hpRiemannThetaLogProfile u : ℝ) : ℂ) *
          Complex.sin (t * (u : ℂ)))
      (Set.Ioi 0) volume := by
  exact hpTheta_mul_complex_sin_integrableOn
    (deriv hpRiemannThetaLogProfile)
    hpRiemannThetaLogProfile_deriv_continuous
    hpRiemannThetaLogProfile_deriv_exp_weighted_integrableOn t

#print axioms hpTheta_mul_complex_exp_integrableOn
#print axioms hpTheta_mul_complex_cos_integrableOn
#print axioms hpTheta_mul_complex_sin_integrableOn
#print axioms hpRiemannThetaLogProfile_cos_integrableOn
#print axioms hpRiemannThetaLogProfile_sin_integrableOn
#print axioms hpRiemannThetaLogProfile_deriv_cos_integrableOn
#print axioms hpRiemannThetaLogProfile_deriv_sin_integrableOn

end HodgeProofHP
LEAN

lake build HodgeProofHP.Stage4ThetaProfileWeightedIntegrability
lake env lean HodgeProofHP/Stage4ThetaTrigonometricIntegrability.lean
lake build HodgeProofHP.Stage4ThetaTrigonometricIntegrability
