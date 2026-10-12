/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenCubicAlgebra
import HodgeProofHP.Stage6ThetaPhiAllMomentsIntegrability
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Direct integral representation of the cubic Jensen polynomial

The same theta kernel determines all four moments. Represent evaluation
by a single signed polynomial weight before estimating cell integrals.
No numerical sign certificate or cubic real-root conclusion is assumed.
-/
noncomputable section
open MeasureTheory
namespace HodgeProofHP

def hpThetaJensenCubicWeight (p u : ℝ) : ℝ :=
  1 + (3 * p / 2) * u ^ 2 + (p ^ 2 / 4) * u ^ 4 + (p ^ 3 / 120) * u ^ 6

theorem hpThetaJensenCubicWeight_mul_kernel (p u : ℝ) :
    hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight p u =
      hpRiemannThetaDifferentialKernel u +
      (3 * p / 2) * (u ^ 2 * hpRiemannThetaDifferentialKernel u) +
      (p ^ 2 / 4) * (u ^ 4 * hpRiemannThetaDifferentialKernel u) +
      (p ^ 3 / 120) * (u ^ 6 * hpRiemannThetaDifferentialKernel u) := by
  unfold hpThetaJensenCubicWeight
  ring

theorem hpThetaJensenCubicWeight_integrableOn (p : ℝ) :
    IntegrableOn (fun u : ℝ =>
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight p u)
      (Set.Ioi 0) volume := by
  have h0 : IntegrableOn hpRiemannThetaDifferentialKernel (Set.Ioi 0) volume := by
    simpa only [pow_zero, one_mul] using hpThetaPhi_natMoment_integrableOn 0
  have h2 := (hpThetaPhi_natMoment_integrableOn 2).const_mul (3 * p / 2)
  have h4 := (hpThetaPhi_natMoment_integrableOn 4).const_mul (p ^ 2 / 4)
  have h6 := (hpThetaPhi_natMoment_integrableOn 6).const_mul (p ^ 3 / 120)
  simp_rw [hpThetaJensenCubicWeight_mul_kernel]
  exact ((h0.add h2).add h4).add h6

theorem hpThetaJensenCubic_eval_eq_integral (p : ℝ) :
    (hpThetaJensenPolynomial 3 0).eval p =
      ∫ u : ℝ in Set.Ioi 0,
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight p u := by
  have h0 : IntegrableOn hpRiemannThetaDifferentialKernel (Set.Ioi 0) volume := by
    simpa only [pow_zero, one_mul] using hpThetaPhi_natMoment_integrableOn 0
  have h2 := (hpThetaPhi_natMoment_integrableOn 2).const_mul (3 * p / 2)
  have h4 := (hpThetaPhi_natMoment_integrableOn 4).const_mul (p ^ 2 / 4)
  have h6 := (hpThetaPhi_natMoment_integrableOn 6).const_mul (p ^ 3 / 120)
  simp_rw [hpThetaJensenCubicWeight_mul_kernel]
  have hadd2 := integral_add h0 h2
  have hadd4 := integral_add (h0.add h2) h4
  have hadd6 := integral_add ((h0.add h2).add h4) h6
  simp only [Pi.add_apply] at hadd2 hadd4 hadd6
  rw [hadd6, hadd4, hadd2,
    integral_const_mul, integral_const_mul, integral_const_mul,
    hpThetaJensenCubic_eval_moments]
  simp only [hpThetaPhiEvenMoment, hpThetaPhiMomentFour, Nat.reduceMul, pow_zero, one_mul]
  ring

theorem hpThetaJensenCubic_eval_eq_finite_add_tail (p : ℝ) :
    (hpThetaJensenPolynomial 3 0).eval p =
      (∫ u : ℝ in Set.Ioo 0 1,
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight p u) +
      (∫ u : ℝ in Set.Ioi 1,
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight p u) := by
  rw [hpThetaJensenCubic_eval_eq_integral]
  have h := intervalIntegral.integral_Ioi_sub_Ioi
    (hpThetaJensenCubicWeight_integrableOn p) (show (0 : ℝ) ≤ 1 by norm_num)
  rw [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num),
    integral_Ioc_eq_integral_Ioo] at h
  linarith

#print axioms hpThetaJensenCubicWeight_mul_kernel
#print axioms hpThetaJensenCubicWeight_integrableOn
#print axioms hpThetaJensenCubic_eval_eq_integral
#print axioms hpThetaJensenCubic_eval_eq_finite_add_tail
end HodgeProofHP
