/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenCNVStrictMomentComparison

/-!
# Actual score moments and the strict half-moment inequality

The substitution x = t^2 identifies all required kernel and score moments.
Applying the strict integral comparison to x^(n+1/2) K(x) gives
(n+1/2) J(n) J(n+2) < (n+3/2) J(n+1)^2.
No integrability or moment-comparison hypothesis is left in that theorem.
-/
noncomputable section
open MeasureTheory Filter
namespace HodgeProofHP

theorem hpThetaCNV_sqrtKernel_substitution_factor (m : ℕ) (t : ℝ) (ht : 0 < t) :
    (2 * t ^ ((2 : ℝ) - 1)) •
        ((t ^ (2 : ℝ)) ^ (((m : ℝ) - 1) / 2) *
          hpRiemannThetaDifferentialKernel (Real.sqrt (t ^ (2 : ℝ)))) =
      2 * (t ^ m * hpRiemannThetaDifferentialKernel t) := by
  have hpow : t * (t ^ (2 : ℝ)) ^ (((m : ℝ) - 1) / 2) = t ^ m := by
    rw [← Real.rpow_mul ht.le]
    calc
      t * t ^ (2 * (((m : ℝ) - 1) / 2)) =
          t ^ (1 + 2 * (((m : ℝ) - 1) / 2)) := by
        rw [Real.rpow_add ht, Real.rpow_one]
      _ = t ^ (m : ℝ) := by congr 1; ring
      _ = t ^ m := Real.rpow_natCast t m
  have ht2 : t ^ (2 : ℝ) = t ^ (2 : ℕ) := by
    simpa only [Nat.cast_ofNat] using Real.rpow_natCast t 2
  have hsqrt : Real.sqrt (t ^ (2 : ℝ)) = t := by
    rw [ht2, Real.sqrt_sq_eq_abs, abs_of_pos ht]
  rw [hsqrt]
  simp only [smul_eq_mul, show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one]
  calc
    _ = 2 * ((t * (t ^ (2 : ℝ)) ^ (((m : ℝ) - 1) / 2)) *
        hpRiemannThetaDifferentialKernel t) := by ring
    _ = _ := by rw [hpow]

theorem hpThetaCNV_sqrtKernelMoment_integrableOn (m : ℕ) :
    IntegrableOn (fun x : ℝ => x ^ (((m : ℝ) - 1) / 2) *
      hpRiemannThetaDifferentialKernel (Real.sqrt x)) (Set.Ioi 0) volume := by
  apply (MeasureTheory.integrableOn_Ioi_comp_rpow_iff
    (fun x : ℝ => x ^ (((m : ℝ) - 1) / 2) *
      hpRiemannThetaDifferentialKernel (Real.sqrt x)) (p := 2) (by norm_num)).mp
  apply Integrable.congr ((hpThetaPhi_natMoment_integrableOn m).const_mul 2)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  symm
  simpa only [abs_of_pos (by norm_num : (0 : ℝ) < 2)] using
    hpThetaCNV_sqrtKernel_substitution_factor m t ht

theorem hpThetaCNV_sqrtKernelMoment_integral (m : ℕ) :
    (∫ x in Set.Ioi (0 : ℝ), x ^ (((m : ℝ) - 1) / 2) *
      hpRiemannThetaDifferentialKernel (Real.sqrt x)) =
      2 * ∫ t in Set.Ioi (0 : ℝ), t ^ m * hpRiemannThetaDifferentialKernel t := by
  have hs := MeasureTheory.integral_comp_rpow_Ioi_of_pos
    (g := fun x : ℝ => x ^ (((m : ℝ) - 1) / 2) *
      hpRiemannThetaDifferentialKernel (Real.sqrt x)) (p := 2) (by norm_num)
  calc
    _ = ∫ t in Set.Ioi (0 : ℝ), (2 * t ^ ((2 : ℝ) - 1)) •
        ((t ^ (2 : ℝ)) ^ (((m : ℝ) - 1) / 2) *
          hpRiemannThetaDifferentialKernel (Real.sqrt (t ^ (2 : ℝ)))) := hs.symm
    _ = ∫ t in Set.Ioi (0 : ℝ), 2 * (t ^ m * hpRiemannThetaDifferentialKernel t) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      exact hpThetaCNV_sqrtKernel_substitution_factor m t ht
    _ = _ := integral_const_mul _ _

theorem hpThetaCNVScore_halfWeight_eq (n : ℕ) (x : ℝ) (hx : 0 < x) :
    hpThetaCNVScore x * (x ^ ((n : ℝ) + 1 / 2) * hpThetaPhiSquareTail x) =
      x ^ ((n : ℝ) + 1 / 2) * hpRiemannThetaDifferentialKernel (Real.sqrt x) := by
  have hK : hpThetaPhiSquareTail x ≠ 0 := (hpThetaPhiSquareTail_pos x hx).ne'
  rw [hpThetaCNVScore_eq_kernel_ratio]
  field_simp
  <;> ring

theorem hpThetaCNVScore_halfWeight_integrableOn (n : ℕ) :
    IntegrableOn (fun x : ℝ => hpThetaCNVScore x *
      (x ^ ((n : ℝ) + 1 / 2) * hpThetaPhiSquareTail x)) (Set.Ioi 0) volume := by
  have hexp : (((2 * n + 2 : ℕ) : ℝ) - 1) / 2 = (n : ℝ) + 1 / 2 := by
    push_cast
    ring
  have h := hpThetaCNV_sqrtKernelMoment_integrableOn (2 * n + 2)
  rw [hexp] at h
  apply Integrable.congr h
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact (hpThetaCNVScore_halfWeight_eq n x hx).symm

theorem hpThetaCNVScore_halfWeight_integral (n : ℕ) :
    (∫ x in Set.Ioi (0 : ℝ), hpThetaCNVScore x *
      (x ^ ((n : ℝ) + 1 / 2) * hpThetaPhiSquareTail x)) =
      ((n : ℝ) + 1 / 2) * hpThetaCNVHalfMoment n := by
  have hexp : (((2 * n + 2 : ℕ) : ℝ) - 1) / 2 = (n : ℝ) + 1 / 2 := by
    push_cast
    ring
  have h := hpThetaCNV_sqrtKernelMoment_integral (2 * n + 2)
  rw [hexp, show 2 * n + 2 = 2 * (n + 1) by omega] at h
  have hkernel : (∫ x in Set.Ioi (0 : ℝ), x ^ ((n : ℝ) + 1 / 2) *
      hpRiemannThetaDifferentialKernel (Real.sqrt x)) =
      2 * hpThetaPhiEvenMoment (n + 1) := h
  calc
    _ = ∫ x in Set.Ioi (0 : ℝ), x ^ ((n : ℝ) + 1 / 2) *
        hpRiemannThetaDifferentialKernel (Real.sqrt x) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      exact hpThetaCNVScore_halfWeight_eq n x hx
    _ = 2 * hpThetaPhiEvenMoment (n + 1) := hkernel
    _ = _ := by
      rw [hpThetaCNVHalfMoment_eq_evenMoment]
      have hn : 2 * (n : ℝ) + 1 ≠ 0 := by positivity
      field_simp
      <;> ring

theorem hpThetaCNV_halfWeight_mul_x (n : ℕ) (x : ℝ) (hx : 0 < x) :
    x * (x ^ ((n : ℝ) + 1 / 2) * hpThetaPhiSquareTail x) =
      x ^ (((n + 1 : ℕ) : ℝ) + 1 / 2) * hpThetaPhiSquareTail x := by
  have he : ((n + 1 : ℕ) : ℝ) + 1 / 2 = 1 + ((n : ℝ) + 1 / 2) := by
    push_cast
    ring
  rw [he, Real.rpow_add hx, Real.rpow_one]
  ring

theorem hpThetaCNVHalfMoment_strict_inequality (n : ℕ) :
    ((n : ℝ) + 1 / 2) * hpThetaCNVHalfMoment n * hpThetaCNVHalfMoment (n + 2) <
      ((n : ℝ) + 3 / 2) * hpThetaCNVHalfMoment (n + 1) ^ 2 := by
  let w : ℝ → ℝ := fun x => x ^ ((n : ℝ) + 1 / 2) * hpThetaPhiSquareTail x
  have hexp (k : ℕ) : ((k + 1 : ℕ) : ℝ) - 1 / 2 = (k : ℝ) + 1 / 2 := by
    push_cast
    ring
  have hw (k : ℕ) : IntegrableOn (fun x : ℝ =>
      x ^ ((k : ℝ) + 1 / 2) * hpThetaPhiSquareTail x) (Set.Ioi 0) volume := by
    simpa only [hexp k] using hpThetaPhiSquareTail_halfMoment_integrableOn (k + 1)
  have hmass (k : ℕ) : (∫ x in Set.Ioi (0 : ℝ),
      x ^ ((k : ℝ) + 1 / 2) * hpThetaPhiSquareTail x) = hpThetaCNVHalfMoment (k + 1) := by
    simp only [hpThetaCNVHalfMoment, hexp k]
  have hxw : IntegrableOn (fun x : ℝ => x * w x) (Set.Ioi 0) volume := by
    apply Integrable.congr (hw (n + 1))
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact (hpThetaCNV_halfWeight_mul_x n x hx).symm
  have hxqw : IntegrableOn (fun x : ℝ => x * hpThetaCNVScore x * w x)
      (Set.Ioi 0) volume := by
    apply Integrable.congr (hpThetaCNVScore_halfWeight_integrableOn (n + 1))
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    change hpThetaCNVScore x *
      (x ^ (((n + 1 : ℕ) : ℝ) + 1 / 2) * hpThetaPhiSquareTail x) =
        x * hpThetaCNVScore x * w x
    rw [← hpThetaCNV_halfWeight_mul_x n x hx]
    dsimp [w]
    ring
  have h := hpThetaCNVScore_weighted_integral_comparison w (hw n) hxw
    (hpThetaCNVScore_halfWeight_integrableOn n) hxqw
    (fun x hx => mul_pos (Real.rpow_pos_of_pos hx _) (hpThetaPhiSquareTail_pos x hx))
  have hxmass : (∫ x in Set.Ioi (0 : ℝ), x * w x) = hpThetaCNVHalfMoment (n + 2) := by
    calc
      _ = ∫ x in Set.Ioi (0 : ℝ),
          x ^ (((n + 1 : ℕ) : ℝ) + 1 / 2) * hpThetaPhiSquareTail x := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x hx
        exact hpThetaCNV_halfWeight_mul_x n x hx
      _ = _ := hmass (n + 1)
  have hxqmass : (∫ x in Set.Ioi (0 : ℝ), x * hpThetaCNVScore x * w x) =
      (((n + 1 : ℕ) : ℝ) + 1 / 2) * hpThetaCNVHalfMoment (n + 1) := by
    calc
      _ = ∫ x in Set.Ioi (0 : ℝ), hpThetaCNVScore x *
          (x ^ (((n + 1 : ℕ) : ℝ) + 1 / 2) * hpThetaPhiSquareTail x) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x hx
        rw [← hpThetaCNV_halfWeight_mul_x n x hx]
        dsimp [w]
        ring
      _ = _ := hpThetaCNVScore_halfWeight_integral (n + 1)
  change (∫ x in Set.Ioi (0 : ℝ), x * w x) *
      (∫ x in Set.Ioi (0 : ℝ), hpThetaCNVScore x *
        (x ^ ((n : ℝ) + 1 / 2) * hpThetaPhiSquareTail x)) <
    (∫ x in Set.Ioi (0 : ℝ), x ^ ((n : ℝ) + 1 / 2) * hpThetaPhiSquareTail x) *
      (∫ x in Set.Ioi (0 : ℝ), x * hpThetaCNVScore x * w x) at h
  rw [hxmass, hpThetaCNVScore_halfWeight_integral, hmass, hxqmass] at h
  push_cast at h
  nlinarith [h]

#print axioms hpThetaCNV_sqrtKernel_substitution_factor
#print axioms hpThetaCNV_sqrtKernelMoment_integrableOn
#print axioms hpThetaCNV_sqrtKernelMoment_integral
#print axioms hpThetaCNVScore_halfWeight_eq
#print axioms hpThetaCNVScore_halfWeight_integrableOn
#print axioms hpThetaCNVScore_halfWeight_integral
#print axioms hpThetaCNV_halfWeight_mul_x
#print axioms hpThetaCNVHalfMoment_strict_inequality
end HodgeProofHP
