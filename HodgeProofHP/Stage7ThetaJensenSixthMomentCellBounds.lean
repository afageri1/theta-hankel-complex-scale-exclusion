/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage6ThetaPhiAllMomentsIntegrability
import HodgeProofHP.Stage5ThetaJensenKernelBounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Sixth-moment cell bounds and finite partition

Extend rectangle integration and telescoping partitions to every natural
power, then specialize to the sixth moment. Existing numerical kernel
certificates can be reused without changing any Stage 5 source.
This module does not yet evaluate the 1600 rational rectangles.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace HodgeProofHP

theorem hpThetaJensen_natPowerCellIntegral_bounds
    (m : ℕ)
    (l r L U : ℝ) (hl : 0 ≤ l) (hlr : l ≤ r) (hL : 0 ≤ L)
    (hbound : ∀ u ∈ Set.Icc l r,
      L ≤ hpRiemannThetaDifferentialKernel u ∧
        hpRiemannThetaDifferentialKernel u ≤ U) :
    l ^ m * L * (r - l) ≤
        (∫ u : ℝ in Set.Ioo l r, u ^ m * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo l r, u ^ m * hpRiemannThetaDifferentialKernel u) ≤
        r ^ m * U * (r - l) := by
  have hint : IntegrableOn
      (fun u : ℝ => u ^ m * hpRiemannThetaDifferentialKernel u)
      (Set.Ioo l r) volume := by
    apply (hpThetaPhi_natMoment_integrableOn m).mono_set
    intro u hu
    exact lt_of_le_of_lt hl hu.1
  have hfinite : volume (Set.Ioo l r) ≠ ⊤ := by simp
  have hlow : ∀ u ∈ Set.Ioo l r,
      l ^ m * L ≤ u ^ m * hpRiemannThetaDifferentialKernel u := by
    intro u hu
    have hu0 := le_trans hl (le_of_lt hu.1)
    have h := hbound u ⟨le_of_lt hu.1, le_of_lt hu.2⟩
    exact mul_le_mul (pow_le_pow_left₀ hl (le_of_lt hu.1) m)
      h.1 hL (pow_nonneg hu0 m)
  have hupp : ∀ u ∈ Set.Ioo l r,
      u ^ m * hpRiemannThetaDifferentialKernel u ≤ r ^ m * U := by
    intro u hu
    have hu0 := le_trans hl (le_of_lt hu.1)
    have h := hbound u ⟨le_of_lt hu.1, le_of_lt hu.2⟩
    exact mul_le_mul (pow_le_pow_left₀ hu0 (le_of_lt hu.2) m)
      h.2 (le_of_lt (hpThetaPhi_pos_on_nonnegative u hu0))
      (pow_nonneg (le_trans hl hlr) m)
  constructor
  · have h := setIntegral_ge_of_const_le_real
      measurableSet_Ioo hfinite hlow hint
    rw [Real.volume_real_Ioo_of_le hlr] at h
    exact h
  · have hneg : ∀ u ∈ Set.Ioo l r,
        -(r ^ m * U) ≤ -(u ^ m * hpRiemannThetaDifferentialKernel u) := by
      intro u hu
      exact neg_le_neg (hupp u hu)
    have h := setIntegral_ge_of_const_le_real
      measurableSet_Ioo hfinite hneg hint.neg
    rw [Real.volume_real_Ioo_of_le hlr, integral_neg] at h
    linarith


theorem hpThetaJensen_sixthCellIntegral_bounds
    (l r L U : ℝ) (hl : 0 ≤ l) (hlr : l ≤ r) (hL : 0 ≤ L)
    (hbound : ∀ u ∈ Set.Icc l r,
      L ≤ hpRiemannThetaDifferentialKernel u ∧
        hpRiemannThetaDifferentialKernel u ≤ U) :
    l ^ 6 * L * (r - l) ≤
        (∫ u : ℝ in Set.Ioo l r, u ^ 6 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo l r, u ^ 6 * hpRiemannThetaDifferentialKernel u) ≤
        r ^ 6 * U * (r - l) :=
  hpThetaJensen_natPowerCellIntegral_bounds 6 l r L U hl hlr hL hbound

theorem hpThetaJensen_sixthCellIntegral_endpoint_bounds
    (l r : ℝ) (hl : 0 ≤ l) (hlr : l ≤ r) :
    l ^ 6 * hpThetaTraceEndpointLower l r * (r - l) ≤
        (∫ u : ℝ in Set.Ioo l r, u ^ 6 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo l r, u ^ 6 * hpRiemannThetaDifferentialKernel u) ≤
        r ^ 6 * hpThetaJensenKernelEndpointUpper l r * (r - l) := by
  apply hpThetaJensen_sixthCellIntegral_bounds l r
    (hpThetaTraceEndpointLower l r) (hpThetaJensenKernelEndpointUpper l r)
    hl hlr (hpThetaTraceEndpointLower_nonneg l r hl)
  intro u hu
  exact ⟨hpThetaJensenKernel_endpointLower_le l r u hl hu.1 hu.2,
    hpThetaJensenKernel_le_endpointUpper l r u hl hu.1 hu.2⟩

theorem hpThetaJensen_natPowerUniformCellIntegral_sum
    (m : ℕ)
    (N : ℕ) (s d : ℝ) (hs : 0 ≤ s) (hd : 0 ≤ d) :
    (∑ k ∈ Finset.range N,
      ∫ u : ℝ in Set.Ioo (s + (k : ℝ) * d) (s + ((k + 1 : ℕ) : ℝ) * d),
        u ^ m * hpRiemannThetaDifferentialKernel u) =
      ∫ u : ℝ in Set.Ioo s (s + (N : ℝ) * d),
        u ^ m * hpRiemannThetaDifferentialKernel u := by
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
      IntervalIntegrable (fun u : ℝ => u ^ m * hpRiemannThetaDifferentialKernel u)
        volume (a k) (a (k + 1)) := by
    intro k hk
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (hab k)).2
    apply (hpThetaPhi_natMoment_integrableOn m).mono_set
    intro u hu
    exact lt_of_le_of_lt (ha k) hu.1
  have hcell : ∀ k : ℕ,
      (∫ u : ℝ in Set.Ioo (a k) (a (k + 1)),
        u ^ m * hpRiemannThetaDifferentialKernel u) =
      ∫ u : ℝ in (a k)..(a (k + 1)),
        u ^ m * hpRiemannThetaDifferentialKernel u := by
    intro k
    rw [intervalIntegral.integral_of_le (hab k), integral_Ioc_eq_integral_Ioo]
  have hsum := intervalIntegral.sum_integral_adjacent_intervals (a := a) hint
  have hend : s ≤ s + (N : ℝ) * d := by
    have hNd : 0 ≤ (N : ℝ) * d := by positivity
    linarith
  calc
    _ = ∑ k ∈ Finset.range N,
        ∫ u : ℝ in (a k)..(a (k + 1)),
          u ^ m * hpRiemannThetaDifferentialKernel u := by
      apply Finset.sum_congr rfl
      intro k hk
      exact hcell k
    _ = ∫ u : ℝ in (a 0)..(a N),
        u ^ m * hpRiemannThetaDifferentialKernel u := hsum
    _ = ∫ u : ℝ in Set.Ioo s (s + (N : ℝ) * d),
        u ^ m * hpRiemannThetaDifferentialKernel u := by
      simp only [a, Nat.cast_zero, zero_mul, add_zero]
      rw [intervalIntegral.integral_of_le hend, integral_Ioc_eq_integral_Ioo]


theorem hpThetaJensen_sixthMoment_1600CellIntegral_sum :
    (∑ k ∈ Finset.range 1600,
      ∫ u : ℝ in Set.Ioo ((k : ℝ) / 1600) (((k + 1 : ℕ) : ℝ) / 1600),
        u ^ 6 * hpRiemannThetaDifferentialKernel u) =
      ∫ u : ℝ in Set.Ioo 0 1, u ^ 6 * hpRiemannThetaDifferentialKernel u := by
  have h := hpThetaJensen_natPowerUniformCellIntegral_sum 6 1600 0
    (1 / 1600) (by norm_num) (by norm_num)
  simpa only [zero_add, mul_one_div, Nat.cast_ofNat,
    show (1600 : ℝ) / 1600 = 1 by norm_num] using h

#print axioms hpThetaJensen_natPowerCellIntegral_bounds
#print axioms hpThetaJensen_sixthCellIntegral_bounds
#print axioms hpThetaJensen_sixthCellIntegral_endpoint_bounds
#print axioms hpThetaJensen_natPowerUniformCellIntegral_sum
#print axioms hpThetaJensen_sixthMoment_1600CellIntegral_sum

end HodgeProofHP
