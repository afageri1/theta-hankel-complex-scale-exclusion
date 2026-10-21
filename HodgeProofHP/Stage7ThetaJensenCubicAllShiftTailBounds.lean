/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenCubicAllShiftIntegrals
import HodgeProofHP.Stage7ThetaJensenNatMomentTailBounds

/-!
# Uniform analytic cubic tail bounds at every natural shift

A cutoff R >= 2*n+7 controls all four moment tails in the signed cubic
weight. The resulting bound is unconditional for every shift and every
real evaluation point. It does not certify finite integral signs, the
sharp defect-step bound, all-shift hyperbolicity, or RH.
-/
noncomputable section
open MeasureTheory
namespace HodgeProofHP

def hpThetaJensenCubicTailCutoff (n : ℕ) : ℝ :=
  ((2 * (n + 3) : ℕ) : ℝ) + 1

def hpThetaJensenCubicShiftTailUpper (n : ℕ) (p R : ℝ) : ℝ :=
  |hpThetaJensenMomentScale n| * hpThetaJensenNatMomentTailUpper (2 * n) R +
    |3 * p * hpThetaJensenMomentScale (n + 1)| *
      hpThetaJensenNatMomentTailUpper (2 * (n + 1)) R +
    |3 * p ^ 2 * hpThetaJensenMomentScale (n + 2)| *
      hpThetaJensenNatMomentTailUpper (2 * (n + 2)) R +
    |p ^ 3 * hpThetaJensenMomentScale (n + 3)| *
      hpThetaJensenNatMomentTailUpper (2 * (n + 3)) R

private theorem hpCubicTail_cutoff_order (n j : ℕ) (R : ℝ)
    (hj : j ≤ 3) (hR : hpThetaJensenCubicTailCutoff n ≤ R) :
    ((2 * (n + j) : ℕ) : ℝ) + 1 ≤ R := by
  have hnat : 2 * (n + j) ≤ 2 * (n + 3) := by omega
  have hcast : ((2 * (n + j) : ℕ) : ℝ) ≤ ((2 * (n + 3) : ℕ) : ℝ) := by
    exact_mod_cast hnat
  unfold hpThetaJensenCubicTailCutoff at hR
  linarith

theorem hpThetaJensenCubicShift_tail_eq_moment_tails
    (n : ℕ) (p R : ℝ) (hR : 0 ≤ R) :
    (∫ u : ℝ in Set.Ioi R,
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicShiftWeight n p u) =
      hpThetaJensenMomentScale n *
        (∫ u : ℝ in Set.Ioi R, u ^ (2 * n) * hpRiemannThetaDifferentialKernel u) +
      (3 * p * hpThetaJensenMomentScale (n + 1)) *
        (∫ u : ℝ in Set.Ioi R, u ^ (2 * (n + 1)) * hpRiemannThetaDifferentialKernel u) +
      (3 * p ^ 2 * hpThetaJensenMomentScale (n + 2)) *
        (∫ u : ℝ in Set.Ioi R, u ^ (2 * (n + 2)) * hpRiemannThetaDifferentialKernel u) +
      (p ^ 3 * hpThetaJensenMomentScale (n + 3)) *
        (∫ u : ℝ in Set.Ioi R, u ^ (2 * (n + 3)) * hpRiemannThetaDifferentialKernel u) := by
  have hi (j : ℕ) : IntegrableOn
      (fun u : ℝ => u ^ (2 * (n + j)) * hpRiemannThetaDifferentialKernel u)
      (Set.Ioi R) volume := by
    apply (hpThetaPhi_evenMoment_integrableOn (n + j)).mono_set
    intro u hu
    exact lt_of_le_of_lt hR hu
  have h0 := (hi 0).const_mul (hpThetaJensenMomentScale n)
  have h1 := (hi 1).const_mul (3 * p * hpThetaJensenMomentScale (n + 1))
  have h2 := (hi 2).const_mul (3 * p ^ 2 * hpThetaJensenMomentScale (n + 2))
  have h3 := (hi 3).const_mul (p ^ 3 * hpThetaJensenMomentScale (n + 3))
  simp only [Nat.add_zero] at h0
  simp_rw [hpThetaJensenCubicShiftWeight_mul_kernel]
  have hadd1 := integral_add h0 h1
  have hadd2 := integral_add (h0.add h1) h2
  have hadd3 := integral_add ((h0.add h1).add h2) h3
  simp only [Pi.add_apply] at hadd1 hadd2 hadd3
  rw [hadd3, hadd2, hadd1, integral_const_mul, integral_const_mul,
    integral_const_mul, integral_const_mul]

theorem hpThetaJensenCubicShift_tail_abs_le
    (n : ℕ) (p R : ℝ) (hR : hpThetaJensenCubicTailCutoff n ≤ R) :
    |∫ u : ℝ in Set.Ioi R,
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicShiftWeight n p u| ≤
        hpThetaJensenCubicShiftTailUpper n p R := by
  have hc := hpCubicTail_cutoff_order n 0 R (by omega) hR
  simp only [Nat.add_zero] at hc
  have hR0 : 0 ≤ R := by
    have hm : (0 : ℝ) ≤ ((2 * n : ℕ) : ℝ) := Nat.cast_nonneg (2 * n)
    linarith
  rw [hpThetaJensenCubicShift_tail_eq_moment_tails n p R hR0]
  have h0 := hpThetaJensen_abs_coeff_natMoment_tail_le
    (hpThetaJensenMomentScale n) (2 * n) R hc
  have h1 := hpThetaJensen_abs_coeff_natMoment_tail_le
    (3 * p * hpThetaJensenMomentScale (n + 1)) (2 * (n + 1)) R
    (hpCubicTail_cutoff_order n 1 R (by omega) hR)
  have h2 := hpThetaJensen_abs_coeff_natMoment_tail_le
    (3 * p ^ 2 * hpThetaJensenMomentScale (n + 2)) (2 * (n + 2)) R
    (hpCubicTail_cutoff_order n 2 R (by omega) hR)
  have h3 := hpThetaJensen_abs_coeff_natMoment_tail_le
    (p ^ 3 * hpThetaJensenMomentScale (n + 3)) (2 * (n + 3)) R
    (hpCubicTail_cutoff_order n 3 R (by omega) hR)
  unfold hpThetaJensenCubicShiftTailUpper
  exact le_trans (abs_add_le _ _)
    (add_le_add (le_trans (abs_add_le _ _)
      (add_le_add (le_trans (abs_add_le _ _) (add_le_add h0 h1)) h2)) h3)

theorem hpThetaJensenCubicShift_eval_eq_cutoff_add_tail
    (n : ℕ) (p R : ℝ) (hR : 0 ≤ R) :
    (hpThetaJensenPolynomial 3 n).eval p =
      (∫ u : ℝ in Set.Ioo 0 R,
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicShiftWeight n p u) +
      (∫ u : ℝ in Set.Ioi R,
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicShiftWeight n p u) := by
  rw [hpThetaJensenCubicShift_eval_eq_integral]
  have h := intervalIntegral.integral_Ioi_sub_Ioi
    (hpThetaJensenCubicShiftWeight_integrableOn n p) hR
  rw [intervalIntegral.integral_of_le hR, integral_Ioc_eq_integral_Ioo] at h
  linarith

theorem hpThetaJensenCubicShift_eval_error_le
    (n : ℕ) (p R : ℝ) (hR : hpThetaJensenCubicTailCutoff n ≤ R) :
    |(hpThetaJensenPolynomial 3 n).eval p -
      (∫ u : ℝ in Set.Ioo 0 R,
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicShiftWeight n p u)| ≤
      hpThetaJensenCubicShiftTailUpper n p R := by
  have hR0 : 0 ≤ R := by
    have hc := hpCubicTail_cutoff_order n 0 R (by omega) hR
    have hm : (0 : ℝ) ≤ ((2 * (n + 0) : ℕ) : ℝ) := Nat.cast_nonneg (2 * (n + 0))
    linarith
  rw [hpThetaJensenCubicShift_eval_eq_cutoff_add_tail n p R hR0, add_sub_cancel_left]
  exact hpThetaJensenCubicShift_tail_abs_le n p R hR

theorem hpThetaJensenCubicShift_eval_error_le_canonical_cutoff (n : ℕ) (p : ℝ) :
    |(hpThetaJensenPolynomial 3 n).eval p -
      (∫ u : ℝ in Set.Ioo 0 (hpThetaJensenCubicTailCutoff n),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicShiftWeight n p u)| ≤
      hpThetaJensenCubicShiftTailUpper n p (hpThetaJensenCubicTailCutoff n) :=
  hpThetaJensenCubicShift_eval_error_le n p _ le_rfl

#print axioms hpThetaJensenCubicShift_tail_eq_moment_tails
#print axioms hpThetaJensenCubicShift_tail_abs_le
#print axioms hpThetaJensenCubicShift_eval_eq_cutoff_add_tail
#print axioms hpThetaJensenCubicShift_eval_error_le
#print axioms hpThetaJensenCubicShift_eval_error_le_canonical_cutoff
end HodgeProofHP
