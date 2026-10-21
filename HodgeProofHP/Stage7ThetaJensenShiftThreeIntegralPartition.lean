/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftThreeIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! Telescope signed weighted cell integrals and assemble one batch.
Numerical evaluation signs are not assumed. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

theorem hpThetaJensenShiftThreeWeight_integrableOn (p : ℝ) :
    IntegrableOn (fun u : ℝ =>
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight p u)
      (Set.Ioi 0) volume := by
  have h := hpThetaJensenCubicShiftWeight_integrableOn 3 p
  simpa only [hpThetaJensenCubicShiftWeight_three] using h

theorem hpThetaJensenShiftThree_signedCellIntegral_bounds
    (p l r KL KU WL WU : ℝ) (hl : 0 ≤ l) (hlr : l ≤ r)
    (hk : ∀ u ∈ Set.Icc l r,
      KL ≤ hpRiemannThetaDifferentialKernel u ∧
        hpRiemannThetaDifferentialKernel u ≤ KU)
    (hw : ∀ u ∈ Set.Icc l r,
      WL ≤ hpThetaJensenShiftThreeWeight p u ∧ hpThetaJensenShiftThreeWeight p u ≤ WU) :
    min (KL * WL) (KU * WL) * (r - l) ≤
        (∫ u : ℝ in Set.Ioo l r,
          hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight p u) ∧
      (∫ u : ℝ in Set.Ioo l r,
          hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight p u) ≤
        max (KL * WU) (KU * WU) * (r - l) := by
  have hw' : ∀ u ∈ Set.Icc l r,
      WL ≤ hpThetaJensenCubicShiftWeight 3 p u ∧
        hpThetaJensenCubicShiftWeight 3 p u ≤ WU := by
    intro u hu
    simpa only [hpThetaJensenCubicShiftWeight_three] using hw u hu
  have h := hpThetaJensenCubicShift_signedCellIntegral_bounds
    3 p l r KL KU WL WU hl hlr hk hw'
  simpa only [hpThetaJensenCubicShiftWeight_three] using h

theorem hpThetaJensenShiftThree_uniformCellIntegral_sum
    (p : ℝ)
    (N : ℕ) (s d : ℝ) (hs : 0 ≤ s) (hd : 0 ≤ d) :
    (∑ k ∈ Finset.range N,
      ∫ u : ℝ in Set.Ioo (s + (k : ℝ) * d) (s + ((k + 1 : ℕ) : ℝ) * d),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight p u) =
      ∫ u : ℝ in Set.Ioo s (s + (N : ℝ) * d),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight p u := by
  let a : ℕ → ℝ := fun k => s + (k : ℝ) * d
  have ha : ∀ k : ℕ, 0 ≤ a k := by
    intro k
    dsimp [a]
    positivity
  have hab : ∀ k : ℕ, a k ≤ a (k + 1) := by
    intro k
    dsimp [a]
    push_cast
    nlinarith
  have hint : ∀ k < N,
      IntervalIntegrable (fun u : ℝ => hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight p u)
        volume (a k) (a (k + 1)) := by
    intro k hk
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (hab k)).2
    apply (hpThetaJensenShiftThreeWeight_integrableOn p).mono_set
    intro u hu
    exact lt_of_le_of_lt (ha k) hu.1
  have hcell : ∀ k : ℕ,
      (∫ u : ℝ in Set.Ioo (a k) (a (k + 1)),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight p u) =
      ∫ u : ℝ in (a k)..(a (k + 1)),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight p u := by
    intro k
    rw [intervalIntegral.integral_of_le (hab k), integral_Ioc_eq_integral_Ioo]
  have hsum := intervalIntegral.sum_integral_adjacent_intervals (a := a) hint
  have hend : s ≤ s + (N : ℝ) * d := by
    have hNd : 0 ≤ (N : ℝ) * d := by positivity
    linarith
  calc
    _ = ∑ k ∈ Finset.range N,
        ∫ u : ℝ in (a k)..(a (k + 1)),
          hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight p u := by
      apply Finset.sum_congr rfl
      intro k hk
      exact hcell k
    _ = ∫ u : ℝ in (a 0)..(a N),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight p u := hsum
    _ = ∫ u : ℝ in Set.Ioo s (s + (N : ℝ) * d),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight p u := by
      simp only [a, Nat.cast_zero, zero_mul, add_zero]
      rw [intervalIntegral.integral_of_le hend, integral_Ioc_eq_integral_Ioo]


theorem hpThetaJensenShiftThree_batchIntegral_of_bounds
    (p s : ℝ) (hs : 0 ≤ s) (KL KU WL WU : ℕ → ℝ)
    (hkernel : ∀ (j : Fin 20) (u : ℝ),
      u ∈ Set.Icc ((s + (j.val : ℝ)) / 1600)
        ((s + (j.val : ℝ) + 1) / 1600) →
      KL j.val ≤ hpRiemannThetaDifferentialKernel u ∧
        hpRiemannThetaDifferentialKernel u ≤ KU j.val)
    (hweight : ∀ (j : Fin 20) (u : ℝ),
      u ∈ Set.Icc ((s + (j.val : ℝ)) / 1600)
        ((s + (j.val : ℝ) + 1) / 1600) →
      WL j.val ≤ hpThetaJensenShiftThreeWeight p u ∧
        hpThetaJensenShiftThreeWeight p u ≤ WU j.val) :
    (∑ j ∈ Finset.range 20, min (KL j * WL j) (KU j * WL j) / 1600) ≤
        (∫ u : ℝ in Set.Ioo (s / 1600) ((s + 20) / 1600),
          hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight p u) ∧
      (∫ u : ℝ in Set.Ioo (s / 1600) ((s + 20) / 1600),
          hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight p u) ≤
        ∑ j ∈ Finset.range 20, max (KL j * WU j) (KU j * WU j) / 1600 := by
  have hcell (j : Fin 20) :
      min (KL j.val * WL j.val) (KU j.val * WL j.val) / 1600 ≤
          (∫ u : ℝ in Set.Ioo ((s + (j.val : ℝ)) / 1600)
            ((s + (j.val : ℝ) + 1) / 1600),
            hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight p u) ∧
        (∫ u : ℝ in Set.Ioo ((s + (j.val : ℝ)) / 1600)
            ((s + (j.val : ℝ) + 1) / 1600),
            hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight p u) ≤
          max (KL j.val * WU j.val) (KU j.val * WU j.val) / 1600 := by
    have hl : 0 ≤ (s + (j.val : ℝ)) / 1600 := by positivity
    have hlr : (s + (j.val : ℝ)) / 1600 ≤
        (s + (j.val : ℝ) + 1) / 1600 := by linarith
    have h := hpThetaJensenShiftThree_signedCellIntegral_bounds p
      ((s + (j.val : ℝ)) / 1600) ((s + (j.val : ℝ) + 1) / 1600)
      (KL j.val) (KU j.val) (WL j.val) (WU j.val) hl hlr
      (hkernel j) (hweight j)
    have hw : (s + (j.val : ℝ) + 1) / 1600 -
        (s + (j.val : ℝ)) / 1600 = 1 / 1600 := by ring
    rw [hw] at h
    simpa only [mul_one_div] using h
  have hsum :
      (∑ j ∈ Finset.range 20,
        ∫ u : ℝ in Set.Ioo ((s + (j : ℝ)) / 1600)
          ((s + (j : ℝ) + 1) / 1600),
          hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight p u) =
      ∫ u : ℝ in Set.Ioo (s / 1600) ((s + 20) / 1600),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight p u := by
    have h := hpThetaJensenShiftThree_uniformCellIntegral_sum p 20
      (s / 1600) (1 / 1600) (by positivity) (by norm_num)
    have hc (j : ℕ) :
        Set.Ioo ((s + (j : ℝ)) / 1600) ((s + (j : ℝ) + 1) / 1600) =
        Set.Ioo (s / 1600 + (j : ℝ) * (1 / 1600))
          (s / 1600 + ((j + 1 : ℕ) : ℝ) * (1 / 1600)) := by
      congr 1 <;> push_cast <;> ring
    simp_rw [hc]
    norm_num only [Nat.cast_ofNat] at h
    have hend : s / 1600 + 1 / 80 = (s + 20) / 1600 := by ring
    rw [hend] at h
    exact h
  have hlow :
      (∑ j ∈ Finset.range 20, min (KL j * WL j) (KU j * WL j) / 1600) ≤
      ∑ j ∈ Finset.range 20,
        ∫ u : ℝ in Set.Ioo ((s + (j : ℝ)) / 1600)
          ((s + (j : ℝ) + 1) / 1600),
          hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight p u := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hcell ⟨j, Finset.mem_range.mp hj⟩).1
  have hupp :
      (∑ j ∈ Finset.range 20,
        ∫ u : ℝ in Set.Ioo ((s + (j : ℝ)) / 1600)
          ((s + (j : ℝ) + 1) / 1600),
          hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight p u) ≤
      ∑ j ∈ Finset.range 20, max (KL j * WU j) (KU j * WU j) / 1600 := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hcell ⟨j, Finset.mem_range.mp hj⟩).2
  rw [hsum] at hlow hupp
  exact ⟨hlow, hupp⟩

#print axioms hpThetaJensenShiftThreeWeight_integrableOn
#print axioms hpThetaJensenShiftThree_signedCellIntegral_bounds
#print axioms hpThetaJensenShiftThree_uniformCellIntegral_sum
#print axioms hpThetaJensenShiftThree_batchIntegral_of_bounds
end HodgeProofHP
