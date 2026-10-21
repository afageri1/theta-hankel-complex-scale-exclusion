/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenEighthMomentRectangles
import HodgeProofHP.Stage7ThetaJensenEighthMomentCellBounds
import HodgeProofHP.Stage7ThetaJensenEighthMomentTailBounds

/-!
# Full certified eighth-moment bounds

Integrate the existing rational rectangles on (0,1) and add the analytic
tail. No higher-degree root hypothesis is used.
-/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

theorem hpThetaJensen_eighthBatchIntegral_of_kernelBounds
    (s : ℝ) (hs : 0 ≤ s) (L U : ℕ → ℝ)
    (hL : ∀ j : Fin 20, 0 ≤ L j.val)
    (hbound : ∀ (j : Fin 20) (u : ℝ),
      u ∈ Set.Icc ((s + (j.val : ℝ)) / 1600)
        ((s + (j.val : ℝ) + 1) / 1600) →
      L j.val ≤ hpRiemannThetaDifferentialKernel u ∧
        hpRiemannThetaDifferentialKernel u ≤ U j.val) :
    (∑ j ∈ Finset.range 20, ((s + (j : ℝ)) / 1600) ^ 8 * L j / 1600) ≤
        (∫ u : ℝ in Set.Ioo (s / 1600) ((s + 20) / 1600),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (s / 1600) ((s + 20) / 1600),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ≤
        ∑ j ∈ Finset.range 20, ((s + (j : ℝ) + 1) / 1600) ^ 8 * U j / 1600 := by
  have hcell (j : Fin 20) :
      ((s + (j.val : ℝ)) / 1600) ^ 8 * L j.val / 1600 ≤
          (∫ u : ℝ in Set.Ioo ((s + (j.val : ℝ)) / 1600)
            ((s + (j.val : ℝ) + 1) / 1600),
            u ^ 8 * hpRiemannThetaDifferentialKernel u) ∧
        (∫ u : ℝ in Set.Ioo ((s + (j.val : ℝ)) / 1600)
            ((s + (j.val : ℝ) + 1) / 1600),
            u ^ 8 * hpRiemannThetaDifferentialKernel u) ≤
          ((s + (j.val : ℝ) + 1) / 1600) ^ 8 * U j.val / 1600 := by
    have hl : 0 ≤ (s + (j.val : ℝ)) / 1600 := by positivity
    have hlr : (s + (j.val : ℝ)) / 1600 ≤
        (s + (j.val : ℝ) + 1) / 1600 := by linarith
    have h := hpThetaJensen_eighthCellIntegral_bounds
      ((s + (j.val : ℝ)) / 1600) ((s + (j.val : ℝ) + 1) / 1600)
      (L j.val) (U j.val) hl hlr (hL j) (hbound j)
    have hw : (s + (j.val : ℝ) + 1) / 1600 -
        (s + (j.val : ℝ)) / 1600 = 1 / 1600 := by ring
    rw [hw] at h
    simpa only [mul_one_div] using h
  have hsum :
      (∑ j ∈ Finset.range 20,
        ∫ u : ℝ in Set.Ioo ((s + (j : ℝ)) / 1600)
          ((s + (j : ℝ) + 1) / 1600),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) =
      ∫ u : ℝ in Set.Ioo (s / 1600) ((s + 20) / 1600),
        u ^ 8 * hpRiemannThetaDifferentialKernel u := by
    have h := hpThetaJensen_natPowerUniformCellIntegral_sum 8 20
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
      (∑ j ∈ Finset.range 20, ((s + (j : ℝ)) / 1600) ^ 8 * L j / 1600) ≤
      ∑ j ∈ Finset.range 20,
        ∫ u : ℝ in Set.Ioo ((s + (j : ℝ)) / 1600)
          ((s + (j : ℝ) + 1) / 1600),
          u ^ 8 * hpRiemannThetaDifferentialKernel u := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hcell ⟨j, Finset.mem_range.mp hj⟩).1
  have hupp :
      (∑ j ∈ Finset.range 20,
        ∫ u : ℝ in Set.Ioo ((s + (j : ℝ)) / 1600)
          ((s + (j : ℝ) + 1) / 1600),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, ((s + (j : ℝ) + 1) / 1600) ^ 8 * U j / 1600 := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hcell ⟨j, Finset.mem_range.mp hj⟩).2
  rw [hsum] at hlow hupp
  exact ⟨hlow, hupp⟩


theorem hpThetaJensenEighthBatch000_integral_bounds :
    hpThetaJensenEighthRectangleLower 0 ≤
        (∫ u : ℝ in Set.Ioo (0 / 80 : ℝ) ((0 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (0 / 80 : ℝ) ((0 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenEighthRectangleUpper 0 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch000Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch000Lower]
  have h := hpThetaJensen_eighthBatchIntegral_of_kernelBounds (0 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch000Lower hpThetaJensenCellsBatch000Upper hL
    hpThetaJensenCellsBatch000_bounds
  simpa only [hpThetaJensenEighthRectangleLower, hpThetaJensenEighthRectangleUpper,
    add_zero, show (0 : ℝ) / 1600 = 0 / 80 by norm_num,
    show ((0 : ℝ) + 20) / 1600 = (0 + 1) / 80 by norm_num] using h

theorem hpThetaJensenEighthBatch001_integral_bounds :
    hpThetaJensenEighthRectangleLower 1 ≤
        (∫ u : ℝ in Set.Ioo (1 / 80 : ℝ) ((1 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (1 / 80 : ℝ) ((1 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenEighthRectangleUpper 1 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch001Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch001Lower]
  have h := hpThetaJensen_eighthBatchIntegral_of_kernelBounds (20 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch001Lower hpThetaJensenCellsBatch001Upper hL
    hpThetaJensenCellsBatch001_bounds
  simpa only [hpThetaJensenEighthRectangleLower, hpThetaJensenEighthRectangleUpper,
    add_zero, show (20 : ℝ) / 1600 = 1 / 80 by norm_num,
    show ((20 : ℝ) + 20) / 1600 = (1 + 1) / 80 by norm_num] using h

theorem hpThetaJensenEighthBatch002_integral_bounds :
    hpThetaJensenEighthRectangleLower 2 ≤
        (∫ u : ℝ in Set.Ioo (2 / 80 : ℝ) ((2 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (2 / 80 : ℝ) ((2 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenEighthRectangleUpper 2 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch002Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch002Lower]
  have h := hpThetaJensen_eighthBatchIntegral_of_kernelBounds (40 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch002Lower hpThetaJensenCellsBatch002Upper hL
    hpThetaJensenCellsBatch002_bounds
  simpa only [hpThetaJensenEighthRectangleLower, hpThetaJensenEighthRectangleUpper,
    add_zero, show (40 : ℝ) / 1600 = 2 / 80 by norm_num,
    show ((40 : ℝ) + 20) / 1600 = (2 + 1) / 80 by norm_num] using h

theorem hpThetaJensenEighthBatch003_integral_bounds :
    hpThetaJensenEighthRectangleLower 3 ≤
        (∫ u : ℝ in Set.Ioo (3 / 80 : ℝ) ((3 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (3 / 80 : ℝ) ((3 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenEighthRectangleUpper 3 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch003Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch003Lower]
  have h := hpThetaJensen_eighthBatchIntegral_of_kernelBounds (60 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch003Lower hpThetaJensenCellsBatch003Upper hL
    hpThetaJensenCellsBatch003_bounds
  simpa only [hpThetaJensenEighthRectangleLower, hpThetaJensenEighthRectangleUpper,
    add_zero, show (60 : ℝ) / 1600 = 3 / 80 by norm_num,
    show ((60 : ℝ) + 20) / 1600 = (3 + 1) / 80 by norm_num] using h

theorem hpThetaJensenEighthBatch004_integral_bounds :
    hpThetaJensenEighthRectangleLower 4 ≤
        (∫ u : ℝ in Set.Ioo (4 / 80 : ℝ) ((4 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (4 / 80 : ℝ) ((4 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenEighthRectangleUpper 4 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch004Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch004Lower]
  have h := hpThetaJensen_eighthBatchIntegral_of_kernelBounds (80 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch004Lower hpThetaJensenCellsBatch004Upper hL
    hpThetaJensenCellsBatch004_bounds
  simpa only [hpThetaJensenEighthRectangleLower, hpThetaJensenEighthRectangleUpper,
    add_zero, show (80 : ℝ) / 1600 = 4 / 80 by norm_num,
    show ((80 : ℝ) + 20) / 1600 = (4 + 1) / 80 by norm_num] using h

theorem hpThetaJensenEighthBatch005_integral_bounds :
    hpThetaJensenEighthRectangleLower 5 ≤
        (∫ u : ℝ in Set.Ioo (5 / 80 : ℝ) ((5 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (5 / 80 : ℝ) ((5 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenEighthRectangleUpper 5 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch005Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch005Lower]
  have h := hpThetaJensen_eighthBatchIntegral_of_kernelBounds (100 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch005Lower hpThetaJensenCellsBatch005Upper hL
    hpThetaJensenCellsBatch005_bounds
  simpa only [hpThetaJensenEighthRectangleLower, hpThetaJensenEighthRectangleUpper,
    add_zero, show (100 : ℝ) / 1600 = 5 / 80 by norm_num,
    show ((100 : ℝ) + 20) / 1600 = (5 + 1) / 80 by norm_num] using h

theorem hpThetaJensenEighthBatch006_integral_bounds :
    hpThetaJensenEighthRectangleLower 6 ≤
        (∫ u : ℝ in Set.Ioo (6 / 80 : ℝ) ((6 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (6 / 80 : ℝ) ((6 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenEighthRectangleUpper 6 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch006Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch006Lower]
  have h := hpThetaJensen_eighthBatchIntegral_of_kernelBounds (120 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch006Lower hpThetaJensenCellsBatch006Upper hL
    hpThetaJensenCellsBatch006_bounds
  simpa only [hpThetaJensenEighthRectangleLower, hpThetaJensenEighthRectangleUpper,
    add_zero, show (120 : ℝ) / 1600 = 6 / 80 by norm_num,
    show ((120 : ℝ) + 20) / 1600 = (6 + 1) / 80 by norm_num] using h

theorem hpThetaJensenEighthBatch007_integral_bounds :
    hpThetaJensenEighthRectangleLower 7 ≤
        (∫ u : ℝ in Set.Ioo (7 / 80 : ℝ) ((7 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (7 / 80 : ℝ) ((7 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenEighthRectangleUpper 7 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch007Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch007Lower]
  have h := hpThetaJensen_eighthBatchIntegral_of_kernelBounds (140 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch007Lower hpThetaJensenCellsBatch007Upper hL
    hpThetaJensenCellsBatch007_bounds
  simpa only [hpThetaJensenEighthRectangleLower, hpThetaJensenEighthRectangleUpper,
    add_zero, show (140 : ℝ) / 1600 = 7 / 80 by norm_num,
    show ((140 : ℝ) + 20) / 1600 = (7 + 1) / 80 by norm_num] using h

theorem hpThetaJensenEighthBatch008_integral_bounds :
    hpThetaJensenEighthRectangleLower 8 ≤
        (∫ u : ℝ in Set.Ioo (8 / 80 : ℝ) ((8 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (8 / 80 : ℝ) ((8 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenEighthRectangleUpper 8 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch008Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch008Lower]
  have h := hpThetaJensen_eighthBatchIntegral_of_kernelBounds (160 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch008Lower hpThetaJensenCellsBatch008Upper hL
    hpThetaJensenCellsBatch008_bounds
  simpa only [hpThetaJensenEighthRectangleLower, hpThetaJensenEighthRectangleUpper,
    add_zero, show (160 : ℝ) / 1600 = 8 / 80 by norm_num,
    show ((160 : ℝ) + 20) / 1600 = (8 + 1) / 80 by norm_num] using h

theorem hpThetaJensenEighthBatch009_integral_bounds :
    hpThetaJensenEighthRectangleLower 9 ≤
        (∫ u : ℝ in Set.Ioo (9 / 80 : ℝ) ((9 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (9 / 80 : ℝ) ((9 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenEighthRectangleUpper 9 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch009Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch009Lower]
  have h := hpThetaJensen_eighthBatchIntegral_of_kernelBounds (180 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch009Lower hpThetaJensenCellsBatch009Upper hL
    hpThetaJensenCellsBatch009_bounds
  simpa only [hpThetaJensenEighthRectangleLower, hpThetaJensenEighthRectangleUpper,
    add_zero, show (180 : ℝ) / 1600 = 9 / 80 by norm_num,
    show ((180 : ℝ) + 20) / 1600 = (9 + 1) / 80 by norm_num] using h

theorem hpThetaJensenEighthBatch010_integral_bounds :
    hpThetaJensenEighthRectangleLower 10 ≤
        (∫ u : ℝ in Set.Ioo (10 / 80 : ℝ) ((10 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (10 / 80 : ℝ) ((10 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenEighthRectangleUpper 10 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch010Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch010Lower]
  have h := hpThetaJensen_eighthBatchIntegral_of_kernelBounds (200 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch010Lower hpThetaJensenCellsBatch010Upper hL
    hpThetaJensenCellsBatch010_bounds
  simpa only [hpThetaJensenEighthRectangleLower, hpThetaJensenEighthRectangleUpper,
    add_zero, show (200 : ℝ) / 1600 = 10 / 80 by norm_num,
    show ((200 : ℝ) + 20) / 1600 = (10 + 1) / 80 by norm_num] using h

theorem hpThetaJensenEighthBatch011_integral_bounds :
    hpThetaJensenEighthRectangleLower 11 ≤
        (∫ u : ℝ in Set.Ioo (11 / 80 : ℝ) ((11 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (11 / 80 : ℝ) ((11 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenEighthRectangleUpper 11 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch011Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch011Lower]
  have h := hpThetaJensen_eighthBatchIntegral_of_kernelBounds (220 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch011Lower hpThetaJensenCellsBatch011Upper hL
    hpThetaJensenCellsBatch011_bounds
  simpa only [hpThetaJensenEighthRectangleLower, hpThetaJensenEighthRectangleUpper,
    add_zero, show (220 : ℝ) / 1600 = 11 / 80 by norm_num,
    show ((220 : ℝ) + 20) / 1600 = (11 + 1) / 80 by norm_num] using h

theorem hpThetaJensenEighthBatch012_integral_bounds :
    hpThetaJensenEighthRectangleLower 12 ≤
        (∫ u : ℝ in Set.Ioo (12 / 80 : ℝ) ((12 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (12 / 80 : ℝ) ((12 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenEighthRectangleUpper 12 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch012Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch012Lower]
  have h := hpThetaJensen_eighthBatchIntegral_of_kernelBounds (240 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch012Lower hpThetaJensenCellsBatch012Upper hL
    hpThetaJensenCellsBatch012_bounds
  simpa only [hpThetaJensenEighthRectangleLower, hpThetaJensenEighthRectangleUpper,
    add_zero, show (240 : ℝ) / 1600 = 12 / 80 by norm_num,
    show ((240 : ℝ) + 20) / 1600 = (12 + 1) / 80 by norm_num] using h

theorem hpThetaJensenEighthBatch013_integral_bounds :
    hpThetaJensenEighthRectangleLower 13 ≤
        (∫ u : ℝ in Set.Ioo (13 / 80 : ℝ) ((13 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (13 / 80 : ℝ) ((13 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenEighthRectangleUpper 13 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch013Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch013Lower]
  have h := hpThetaJensen_eighthBatchIntegral_of_kernelBounds (260 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch013Lower hpThetaJensenCellsBatch013Upper hL
    hpThetaJensenCellsBatch013_bounds
  simpa only [hpThetaJensenEighthRectangleLower, hpThetaJensenEighthRectangleUpper,
    add_zero, show (260 : ℝ) / 1600 = 13 / 80 by norm_num,
    show ((260 : ℝ) + 20) / 1600 = (13 + 1) / 80 by norm_num] using h

theorem hpThetaJensenEighthBatch014_integral_bounds :
    hpThetaJensenEighthRectangleLower 14 ≤
        (∫ u : ℝ in Set.Ioo (14 / 80 : ℝ) ((14 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (14 / 80 : ℝ) ((14 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenEighthRectangleUpper 14 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch014Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch014Lower]
  have h := hpThetaJensen_eighthBatchIntegral_of_kernelBounds (280 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch014Lower hpThetaJensenCellsBatch014Upper hL
    hpThetaJensenCellsBatch014_bounds
  simpa only [hpThetaJensenEighthRectangleLower, hpThetaJensenEighthRectangleUpper,
    add_zero, show (280 : ℝ) / 1600 = 14 / 80 by norm_num,
    show ((280 : ℝ) + 20) / 1600 = (14 + 1) / 80 by norm_num] using h

theorem hpThetaJensenEighthBatch015_integral_bounds :
    hpThetaJensenEighthRectangleLower 15 ≤
        (∫ u : ℝ in Set.Ioo (15 / 80 : ℝ) ((15 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (15 / 80 : ℝ) ((15 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenEighthRectangleUpper 15 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch015Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch015Lower]
  have h := hpThetaJensen_eighthBatchIntegral_of_kernelBounds (300 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch015Lower hpThetaJensenCellsBatch015Upper hL
    hpThetaJensenCellsBatch015_bounds
  simpa only [hpThetaJensenEighthRectangleLower, hpThetaJensenEighthRectangleUpper,
    add_zero, show (300 : ℝ) / 1600 = 15 / 80 by norm_num,
    show ((300 : ℝ) + 20) / 1600 = (15 + 1) / 80 by norm_num] using h

theorem hpThetaJensenEighthBatch016_integral_bounds :
    hpThetaJensenEighthRectangleLower 16 ≤
        (∫ u : ℝ in Set.Ioo (16 / 80 : ℝ) ((16 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (16 / 80 : ℝ) ((16 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenEighthRectangleUpper 16 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch016Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch016Lower]
  have h := hpThetaJensen_eighthBatchIntegral_of_kernelBounds (320 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch016Lower hpThetaJensenCellsBatch016Upper hL
    hpThetaJensenCellsBatch016_bounds
  simpa only [hpThetaJensenEighthRectangleLower, hpThetaJensenEighthRectangleUpper,
    add_zero, show (320 : ℝ) / 1600 = 16 / 80 by norm_num,
    show ((320 : ℝ) + 20) / 1600 = (16 + 1) / 80 by norm_num] using h

theorem hpThetaJensenEighthBatch017_integral_bounds :
    hpThetaJensenEighthRectangleLower 17 ≤
        (∫ u : ℝ in Set.Ioo (17 / 80 : ℝ) ((17 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (17 / 80 : ℝ) ((17 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenEighthRectangleUpper 17 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch017Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch017Lower]
  have h := hpThetaJensen_eighthBatchIntegral_of_kernelBounds (340 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch017Lower hpThetaJensenCellsBatch017Upper hL
    hpThetaJensenCellsBatch017_bounds
  simpa only [hpThetaJensenEighthRectangleLower, hpThetaJensenEighthRectangleUpper,
    add_zero, show (340 : ℝ) / 1600 = 17 / 80 by norm_num,
    show ((340 : ℝ) + 20) / 1600 = (17 + 1) / 80 by norm_num] using h

theorem hpThetaJensenEighthBatch018_integral_bounds :
    hpThetaJensenEighthRectangleLower 18 ≤
        (∫ u : ℝ in Set.Ioo (18 / 80 : ℝ) ((18 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (18 / 80 : ℝ) ((18 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenEighthRectangleUpper 18 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch018Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch018Lower]
  have h := hpThetaJensen_eighthBatchIntegral_of_kernelBounds (360 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch018Lower hpThetaJensenCellsBatch018Upper hL
    hpThetaJensenCellsBatch018_bounds
  simpa only [hpThetaJensenEighthRectangleLower, hpThetaJensenEighthRectangleUpper,
    add_zero, show (360 : ℝ) / 1600 = 18 / 80 by norm_num,
    show ((360 : ℝ) + 20) / 1600 = (18 + 1) / 80 by norm_num] using h

theorem hpThetaJensenEighthBatch019_integral_bounds :
    hpThetaJensenEighthRectangleLower 19 ≤
        (∫ u : ℝ in Set.Ioo (19 / 80 : ℝ) ((19 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (19 / 80 : ℝ) ((19 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenEighthRectangleUpper 19 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch019Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch019Lower]
  have h := hpThetaJensen_eighthBatchIntegral_of_kernelBounds (380 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch019Lower hpThetaJensenCellsBatch019Upper hL
    hpThetaJensenCellsBatch019_bounds
  simpa only [hpThetaJensenEighthRectangleLower, hpThetaJensenEighthRectangleUpper,
    add_zero, show (380 : ℝ) / 1600 = 19 / 80 by norm_num,
    show ((380 : ℝ) + 20) / 1600 = (19 + 1) / 80 by norm_num] using h

theorem hpThetaJensenEighthBatch020_integral_bounds :
    hpThetaJensenEighthRectangleLower 20 ≤
        (∫ u : ℝ in Set.Ioo (20 / 80 : ℝ) ((20 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (20 / 80 : ℝ) ((20 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenEighthRectangleUpper 20 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch020Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch020Lower]
  have h := hpThetaJensen_eighthBatchIntegral_of_kernelBounds (400 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch020Lower hpThetaJensenCellsBatch020Upper hL
    hpThetaJensenCellsBatch020_bounds
  simpa only [hpThetaJensenEighthRectangleLower, hpThetaJensenEighthRectangleUpper,
    add_zero, show (400 : ℝ) / 1600 = 20 / 80 by norm_num,
    show ((400 : ℝ) + 20) / 1600 = (20 + 1) / 80 by norm_num] using h

theorem hpThetaJensenEighthBatch021_integral_bounds :
    hpThetaJensenEighthRectangleLower 21 ≤
        (∫ u : ℝ in Set.Ioo (21 / 80 : ℝ) ((21 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (21 / 80 : ℝ) ((21 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenEighthRectangleUpper 21 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch021Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch021Lower]
  have h := hpThetaJensen_eighthBatchIntegral_of_kernelBounds (420 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch021Lower hpThetaJensenCellsBatch021Upper hL
    hpThetaJensenCellsBatch021_bounds
  simpa only [hpThetaJensenEighthRectangleLower, hpThetaJensenEighthRectangleUpper,
    add_zero, show (420 : ℝ) / 1600 = 21 / 80 by norm_num,
    show ((420 : ℝ) + 20) / 1600 = (21 + 1) / 80 by norm_num] using h

theorem hpThetaJensenEighthBatch022_integral_bounds :
    hpThetaJensenEighthRectangleLower 22 ≤
        (∫ u : ℝ in Set.Ioo (22 / 80 : ℝ) ((22 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (22 / 80 : ℝ) ((22 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenEighthRectangleUpper 22 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch022Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch022Lower]
  have h := hpThetaJensen_eighthBatchIntegral_of_kernelBounds (440 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch022Lower hpThetaJensenCellsBatch022Upper hL
    hpThetaJensenCellsBatch022_bounds
  simpa only [hpThetaJensenEighthRectangleLower, hpThetaJensenEighthRectangleUpper,
    add_zero, show (440 : ℝ) / 1600 = 22 / 80 by norm_num,
    show ((440 : ℝ) + 20) / 1600 = (22 + 1) / 80 by norm_num] using h

theorem hpThetaJensenEighthBatch023_integral_bounds :
    hpThetaJensenEighthRectangleLower 23 ≤
        (∫ u : ℝ in Set.Ioo (23 / 80 : ℝ) ((23 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (23 / 80 : ℝ) ((23 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenEighthRectangleUpper 23 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch023Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch023Lower]
  have h := hpThetaJensen_eighthBatchIntegral_of_kernelBounds (460 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch023Lower hpThetaJensenCellsBatch023Upper hL
    hpThetaJensenCellsBatch023_bounds
  simpa only [hpThetaJensenEighthRectangleLower, hpThetaJensenEighthRectangleUpper,
    add_zero, show (460 : ℝ) / 1600 = 23 / 80 by norm_num,
    show ((460 : ℝ) + 20) / 1600 = (23 + 1) / 80 by norm_num] using h

theorem hpThetaJensenEighthBatch024_integral_bounds :
    hpThetaJensenEighthRectangleLower 24 ≤
        (∫ u : ℝ in Set.Ioo (24 / 80 : ℝ) ((24 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (24 / 80 : ℝ) ((24 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenEighthRectangleUpper 24 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch024Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch024Lower]
  have h := hpThetaJensen_eighthBatchIntegral_of_kernelBounds (480 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch024Lower hpThetaJensenCellsBatch024Upper hL
    hpThetaJensenCellsBatch024_bounds
  simpa only [hpThetaJensenEighthRectangleLower, hpThetaJensenEighthRectangleUpper,
    add_zero, show (480 : ℝ) / 1600 = 24 / 80 by norm_num,
    show ((480 : ℝ) + 20) / 1600 = (24 + 1) / 80 by norm_num] using h

theorem hpThetaJensenEighthBatch025_integral_bounds :
    hpThetaJensenEighthRectangleLower 25 ≤
        (∫ u : ℝ in Set.Ioo (25 / 80 : ℝ) ((25 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (25 / 80 : ℝ) ((25 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenEighthRectangleUpper 25 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch025Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch025Lower]
  have h := hpThetaJensen_eighthBatchIntegral_of_kernelBounds (500 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch025Lower hpThetaJensenCellsBatch025Upper hL
    hpThetaJensenCellsBatch025_bounds
  simpa only [hpThetaJensenEighthRectangleLower, hpThetaJensenEighthRectangleUpper,
    add_zero, show (500 : ℝ) / 1600 = 25 / 80 by norm_num,
    show ((500 : ℝ) + 20) / 1600 = (25 + 1) / 80 by norm_num] using h

theorem hpThetaJensenEighthBatch026_integral_bounds :
    hpThetaJensenEighthRectangleLower 26 ≤
        (∫ u : ℝ in Set.Ioo (26 / 80 : ℝ) ((26 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (26 / 80 : ℝ) ((26 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenEighthRectangleUpper 26 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch026Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch026Lower]
  have h := hpThetaJensen_eighthBatchIntegral_of_kernelBounds (520 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch026Lower hpThetaJensenCellsBatch026Upper hL
    hpThetaJensenCellsBatch026_bounds
  simpa only [hpThetaJensenEighthRectangleLower, hpThetaJensenEighthRectangleUpper,
    add_zero, show (520 : ℝ) / 1600 = 26 / 80 by norm_num,
    show ((520 : ℝ) + 20) / 1600 = (26 + 1) / 80 by norm_num] using h

theorem hpThetaJensenEighthBatch027_integral_bounds :
    hpThetaJensenEighthRectangleLower 27 ≤
        (∫ u : ℝ in Set.Ioo (27 / 80 : ℝ) ((27 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (27 / 80 : ℝ) ((27 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenEighthRectangleUpper 27 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch027Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch027Lower]
  have h := hpThetaJensen_eighthBatchIntegral_of_kernelBounds (540 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch027Lower hpThetaJensenCellsBatch027Upper hL
    hpThetaJensenCellsBatch027_bounds
  simpa only [hpThetaJensenEighthRectangleLower, hpThetaJensenEighthRectangleUpper,
    add_zero, show (540 : ℝ) / 1600 = 27 / 80 by norm_num,
    show ((540 : ℝ) + 20) / 1600 = (27 + 1) / 80 by norm_num] using h

theorem hpThetaJensenEighthBatch028_integral_bounds :
    hpThetaJensenEighthRectangleLower 28 ≤
        (∫ u : ℝ in Set.Ioo (28 / 80 : ℝ) ((28 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (28 / 80 : ℝ) ((28 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenEighthRectangleUpper 28 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch028Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch028Lower]
  have h := hpThetaJensen_eighthBatchIntegral_of_kernelBounds (560 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch028Lower hpThetaJensenCellsBatch028Upper hL
    hpThetaJensenCellsBatch028_bounds
  simpa only [hpThetaJensenEighthRectangleLower, hpThetaJensenEighthRectangleUpper,
    add_zero, show (560 : ℝ) / 1600 = 28 / 80 by norm_num,
    show ((560 : ℝ) + 20) / 1600 = (28 + 1) / 80 by norm_num] using h

theorem hpThetaJensenEighthBatch029_integral_bounds :
    hpThetaJensenEighthRectangleLower 29 ≤
        (∫ u : ℝ in Set.Ioo (29 / 80 : ℝ) ((29 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (29 / 80 : ℝ) ((29 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenEighthRectangleUpper 29 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch029Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch029Lower]
  have h := hpThetaJensen_eighthBatchIntegral_of_kernelBounds (580 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch029Lower hpThetaJensenCellsBatch029Upper hL
    hpThetaJensenCellsBatch029_bounds
  simpa only [hpThetaJensenEighthRectangleLower, hpThetaJensenEighthRectangleUpper,
    add_zero, show (580 : ℝ) / 1600 = 29 / 80 by norm_num,
    show ((580 : ℝ) + 20) / 1600 = (29 + 1) / 80 by norm_num] using h

theorem hpThetaJensenEighthBatch030_integral_bounds :
    hpThetaJensenEighthRectangleLower 30 ≤
        (∫ u : ℝ in Set.Ioo (30 / 80 : ℝ) ((30 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (30 / 80 : ℝ) ((30 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenEighthRectangleUpper 30 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch030Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch030Lower]
  have h := hpThetaJensen_eighthBatchIntegral_of_kernelBounds (600 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch030Lower hpThetaJensenCellsBatch030Upper hL
    hpThetaJensenCellsBatch030_bounds
  simpa only [hpThetaJensenEighthRectangleLower, hpThetaJensenEighthRectangleUpper,
    add_zero, show (600 : ℝ) / 1600 = 30 / 80 by norm_num,
    show ((600 : ℝ) + 20) / 1600 = (30 + 1) / 80 by norm_num] using h

theorem hpThetaJensenEighthBatch031_integral_bounds :
    hpThetaJensenEighthRectangleLower 31 ≤
        (∫ u : ℝ in Set.Ioo (31 / 80 : ℝ) ((31 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (31 / 80 : ℝ) ((31 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenEighthRectangleUpper 31 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch031Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch031Lower]
  have h := hpThetaJensen_eighthBatchIntegral_of_kernelBounds (620 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch031Lower hpThetaJensenCellsBatch031Upper hL
    hpThetaJensenCellsBatch031_bounds
  simpa only [hpThetaJensenEighthRectangleLower, hpThetaJensenEighthRectangleUpper,
    add_zero, show (620 : ℝ) / 1600 = 31 / 80 by norm_num,
    show ((620 : ℝ) + 20) / 1600 = (31 + 1) / 80 by norm_num] using h

theorem hpThetaJensenEighthBatch032_integral_bounds :
    hpThetaJensenEighthRectangleLower 32 ≤
        (∫ u : ℝ in Set.Ioo (32 / 80 : ℝ) ((32 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (32 / 80 : ℝ) ((32 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenEighthRectangleUpper 32 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch032Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch032Lower]
  have h := hpThetaJensen_eighthBatchIntegral_of_kernelBounds (640 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch032Lower hpThetaJensenCellsBatch032Upper hL
    hpThetaJensenCellsBatch032_bounds
  simpa only [hpThetaJensenEighthRectangleLower, hpThetaJensenEighthRectangleUpper,
    add_zero, show (640 : ℝ) / 1600 = 32 / 80 by norm_num,
    show ((640 : ℝ) + 20) / 1600 = (32 + 1) / 80 by norm_num] using h

theorem hpThetaJensenEighthBatch033_integral_bounds :
    hpThetaJensenEighthRectangleLower 33 ≤
        (∫ u : ℝ in Set.Ioo (33 / 80 : ℝ) ((33 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (33 / 80 : ℝ) ((33 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenEighthRectangleUpper 33 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch033Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch033Lower]
  have h := hpThetaJensen_eighthBatchIntegral_of_kernelBounds (660 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch033Lower hpThetaJensenCellsBatch033Upper hL
    hpThetaJensenCellsBatch033_bounds
  simpa only [hpThetaJensenEighthRectangleLower, hpThetaJensenEighthRectangleUpper,
    add_zero, show (660 : ℝ) / 1600 = 33 / 80 by norm_num,
    show ((660 : ℝ) + 20) / 1600 = (33 + 1) / 80 by norm_num] using h

theorem hpThetaJensenEighthBatch034_integral_bounds :
    hpThetaJensenEighthRectangleLower 34 ≤
        (∫ u : ℝ in Set.Ioo (34 / 80 : ℝ) ((34 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (34 / 80 : ℝ) ((34 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenEighthRectangleUpper 34 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch034Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch034Lower]
  have h := hpThetaJensen_eighthBatchIntegral_of_kernelBounds (680 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch034Lower hpThetaJensenCellsBatch034Upper hL
    hpThetaJensenCellsBatch034_bounds
  simpa only [hpThetaJensenEighthRectangleLower, hpThetaJensenEighthRectangleUpper,
    add_zero, show (680 : ℝ) / 1600 = 34 / 80 by norm_num,
    show ((680 : ℝ) + 20) / 1600 = (34 + 1) / 80 by norm_num] using h

theorem hpThetaJensenEighthBatch035_integral_bounds :
    hpThetaJensenEighthRectangleLower 35 ≤
        (∫ u : ℝ in Set.Ioo (35 / 80 : ℝ) ((35 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (35 / 80 : ℝ) ((35 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenEighthRectangleUpper 35 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch035Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch035Lower]
  have h := hpThetaJensen_eighthBatchIntegral_of_kernelBounds (700 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch035Lower hpThetaJensenCellsBatch035Upper hL
    hpThetaJensenCellsBatch035_bounds
  simpa only [hpThetaJensenEighthRectangleLower, hpThetaJensenEighthRectangleUpper,
    add_zero, show (700 : ℝ) / 1600 = 35 / 80 by norm_num,
    show ((700 : ℝ) + 20) / 1600 = (35 + 1) / 80 by norm_num] using h

theorem hpThetaJensenEighthBatch036_integral_bounds :
    hpThetaJensenEighthRectangleLower 36 ≤
        (∫ u : ℝ in Set.Ioo (36 / 80 : ℝ) ((36 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (36 / 80 : ℝ) ((36 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenEighthRectangleUpper 36 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch036Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch036Lower]
  have h := hpThetaJensen_eighthBatchIntegral_of_kernelBounds (720 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch036Lower hpThetaJensenCellsBatch036Upper hL
    hpThetaJensenCellsBatch036_bounds
  simpa only [hpThetaJensenEighthRectangleLower, hpThetaJensenEighthRectangleUpper,
    add_zero, show (720 : ℝ) / 1600 = 36 / 80 by norm_num,
    show ((720 : ℝ) + 20) / 1600 = (36 + 1) / 80 by norm_num] using h

theorem hpThetaJensenEighthBatch037_integral_bounds :
    hpThetaJensenEighthRectangleLower 37 ≤
        (∫ u : ℝ in Set.Ioo (37 / 80 : ℝ) ((37 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (37 / 80 : ℝ) ((37 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenEighthRectangleUpper 37 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch037Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch037Lower]
  have h := hpThetaJensen_eighthBatchIntegral_of_kernelBounds (740 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch037Lower hpThetaJensenCellsBatch037Upper hL
    hpThetaJensenCellsBatch037_bounds
  simpa only [hpThetaJensenEighthRectangleLower, hpThetaJensenEighthRectangleUpper,
    add_zero, show (740 : ℝ) / 1600 = 37 / 80 by norm_num,
    show ((740 : ℝ) + 20) / 1600 = (37 + 1) / 80 by norm_num] using h

theorem hpThetaJensenEighthBatch038_integral_bounds :
    hpThetaJensenEighthRectangleLower 38 ≤
        (∫ u : ℝ in Set.Ioo (38 / 80 : ℝ) ((38 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (38 / 80 : ℝ) ((38 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenEighthRectangleUpper 38 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch038Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch038Lower]
  have h := hpThetaJensen_eighthBatchIntegral_of_kernelBounds (760 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch038Lower hpThetaJensenCellsBatch038Upper hL
    hpThetaJensenCellsBatch038_bounds
  simpa only [hpThetaJensenEighthRectangleLower, hpThetaJensenEighthRectangleUpper,
    add_zero, show (760 : ℝ) / 1600 = 38 / 80 by norm_num,
    show ((760 : ℝ) + 20) / 1600 = (38 + 1) / 80 by norm_num] using h

theorem hpThetaJensenEighthBatch039_integral_bounds :
    hpThetaJensenEighthRectangleLower 39 ≤
        (∫ u : ℝ in Set.Ioo (39 / 80 : ℝ) ((39 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (39 / 80 : ℝ) ((39 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenEighthRectangleUpper 39 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch039Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch039Lower]
  have h := hpThetaJensen_eighthBatchIntegral_of_kernelBounds (780 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch039Lower hpThetaJensenCellsBatch039Upper hL
    hpThetaJensenCellsBatch039_bounds
  simpa only [hpThetaJensenEighthRectangleLower, hpThetaJensenEighthRectangleUpper,
    add_zero, show (780 : ℝ) / 1600 = 39 / 80 by norm_num,
    show ((780 : ℝ) + 20) / 1600 = (39 + 1) / 80 by norm_num] using h

theorem hpThetaJensenEighthBatch040_integral_bounds :
    hpThetaJensenEighthRectangleLower 40 ≤
        (∫ u : ℝ in Set.Ioo (40 / 80 : ℝ) ((40 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (40 / 80 : ℝ) ((40 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenEighthRectangleUpper 40 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch040Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch040Lower]
  have h := hpThetaJensen_eighthBatchIntegral_of_kernelBounds (800 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch040Lower hpThetaJensenCellsBatch040Upper hL
    hpThetaJensenCellsBatch040_bounds
  simpa only [hpThetaJensenEighthRectangleLower, hpThetaJensenEighthRectangleUpper,
    add_zero, show (800 : ℝ) / 1600 = 40 / 80 by norm_num,
    show ((800 : ℝ) + 20) / 1600 = (40 + 1) / 80 by norm_num] using h

theorem hpThetaJensenEighthBatch041_integral_bounds :
    hpThetaJensenEighthRectangleLower 41 ≤
        (∫ u : ℝ in Set.Ioo (41 / 80 : ℝ) ((41 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (41 / 80 : ℝ) ((41 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenEighthRectangleUpper 41 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch041Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch041Lower]
  have h := hpThetaJensen_eighthBatchIntegral_of_kernelBounds (820 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch041Lower hpThetaJensenCellsBatch041Upper hL
    hpThetaJensenCellsBatch041_bounds
  simpa only [hpThetaJensenEighthRectangleLower, hpThetaJensenEighthRectangleUpper,
    add_zero, show (820 : ℝ) / 1600 = 41 / 80 by norm_num,
    show ((820 : ℝ) + 20) / 1600 = (41 + 1) / 80 by norm_num] using h

theorem hpThetaJensenEighthBatch042_integral_bounds :
    hpThetaJensenEighthRectangleLower 42 ≤
        (∫ u : ℝ in Set.Ioo (42 / 80 : ℝ) ((42 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (42 / 80 : ℝ) ((42 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenEighthRectangleUpper 42 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch042Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch042Lower]
  have h := hpThetaJensen_eighthBatchIntegral_of_kernelBounds (840 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch042Lower hpThetaJensenCellsBatch042Upper hL
    hpThetaJensenCellsBatch042_bounds
  simpa only [hpThetaJensenEighthRectangleLower, hpThetaJensenEighthRectangleUpper,
    add_zero, show (840 : ℝ) / 1600 = 42 / 80 by norm_num,
    show ((840 : ℝ) + 20) / 1600 = (42 + 1) / 80 by norm_num] using h

theorem hpThetaJensenEighthBatch043_integral_bounds :
    hpThetaJensenEighthRectangleLower 43 ≤
        (∫ u : ℝ in Set.Ioo (43 / 80 : ℝ) ((43 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (43 / 80 : ℝ) ((43 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenEighthRectangleUpper 43 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch043Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch043Lower]
  have h := hpThetaJensen_eighthBatchIntegral_of_kernelBounds (860 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch043Lower hpThetaJensenCellsBatch043Upper hL
    hpThetaJensenCellsBatch043_bounds
  simpa only [hpThetaJensenEighthRectangleLower, hpThetaJensenEighthRectangleUpper,
    add_zero, show (860 : ℝ) / 1600 = 43 / 80 by norm_num,
    show ((860 : ℝ) + 20) / 1600 = (43 + 1) / 80 by norm_num] using h

theorem hpThetaJensenEighthBatch044_integral_bounds :
    hpThetaJensenEighthRectangleLower 44 ≤
        (∫ u : ℝ in Set.Ioo (44 / 80 : ℝ) ((44 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (44 / 80 : ℝ) ((44 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenEighthRectangleUpper 44 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch044Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch044Lower]
  have h := hpThetaJensen_eighthBatchIntegral_of_kernelBounds (880 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch044Lower hpThetaJensenCellsBatch044Upper hL
    hpThetaJensenCellsBatch044_bounds
  simpa only [hpThetaJensenEighthRectangleLower, hpThetaJensenEighthRectangleUpper,
    add_zero, show (880 : ℝ) / 1600 = 44 / 80 by norm_num,
    show ((880 : ℝ) + 20) / 1600 = (44 + 1) / 80 by norm_num] using h

theorem hpThetaJensenEighthBatch045_integral_bounds :
    hpThetaJensenEighthRectangleLower 45 ≤
        (∫ u : ℝ in Set.Ioo (45 / 80 : ℝ) ((45 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (45 / 80 : ℝ) ((45 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenEighthRectangleUpper 45 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch045Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch045Lower]
  have h := hpThetaJensen_eighthBatchIntegral_of_kernelBounds (900 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch045Lower hpThetaJensenCellsBatch045Upper hL
    hpThetaJensenCellsBatch045_bounds
  simpa only [hpThetaJensenEighthRectangleLower, hpThetaJensenEighthRectangleUpper,
    add_zero, show (900 : ℝ) / 1600 = 45 / 80 by norm_num,
    show ((900 : ℝ) + 20) / 1600 = (45 + 1) / 80 by norm_num] using h

theorem hpThetaJensenEighthBatch046_integral_bounds :
    hpThetaJensenEighthRectangleLower 46 ≤
        (∫ u : ℝ in Set.Ioo (46 / 80 : ℝ) ((46 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (46 / 80 : ℝ) ((46 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenEighthRectangleUpper 46 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch046Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch046Lower]
  have h := hpThetaJensen_eighthBatchIntegral_of_kernelBounds (920 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch046Lower hpThetaJensenCellsBatch046Upper hL
    hpThetaJensenCellsBatch046_bounds
  simpa only [hpThetaJensenEighthRectangleLower, hpThetaJensenEighthRectangleUpper,
    add_zero, show (920 : ℝ) / 1600 = 46 / 80 by norm_num,
    show ((920 : ℝ) + 20) / 1600 = (46 + 1) / 80 by norm_num] using h

theorem hpThetaJensenEighthBatch047_integral_bounds :
    hpThetaJensenEighthRectangleLower 47 ≤
        (∫ u : ℝ in Set.Ioo (47 / 80 : ℝ) ((47 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (47 / 80 : ℝ) ((47 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenEighthRectangleUpper 47 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch047Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch047Lower]
  have h := hpThetaJensen_eighthBatchIntegral_of_kernelBounds (940 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch047Lower hpThetaJensenCellsBatch047Upper hL
    hpThetaJensenCellsBatch047_bounds
  simpa only [hpThetaJensenEighthRectangleLower, hpThetaJensenEighthRectangleUpper,
    add_zero, show (940 : ℝ) / 1600 = 47 / 80 by norm_num,
    show ((940 : ℝ) + 20) / 1600 = (47 + 1) / 80 by norm_num] using h

theorem hpThetaJensenEighthBatch048_integral_bounds :
    hpThetaJensenEighthRectangleLower 48 ≤
        (∫ u : ℝ in Set.Ioo (48 / 80 : ℝ) ((48 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (48 / 80 : ℝ) ((48 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenEighthRectangleUpper 48 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch048Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch048Lower]
  have h := hpThetaJensen_eighthBatchIntegral_of_kernelBounds (960 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch048Lower hpThetaJensenCellsBatch048Upper hL
    hpThetaJensenCellsBatch048_bounds
  simpa only [hpThetaJensenEighthRectangleLower, hpThetaJensenEighthRectangleUpper,
    add_zero, show (960 : ℝ) / 1600 = 48 / 80 by norm_num,
    show ((960 : ℝ) + 20) / 1600 = (48 + 1) / 80 by norm_num] using h

theorem hpThetaJensenEighthBatch049_integral_bounds :
    hpThetaJensenEighthRectangleLower 49 ≤
        (∫ u : ℝ in Set.Ioo (49 / 80 : ℝ) ((49 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (49 / 80 : ℝ) ((49 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenEighthRectangleUpper 49 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch049Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch049Lower]
  have h := hpThetaJensen_eighthBatchIntegral_of_kernelBounds (980 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch049Lower hpThetaJensenCellsBatch049Upper hL
    hpThetaJensenCellsBatch049_bounds
  simpa only [hpThetaJensenEighthRectangleLower, hpThetaJensenEighthRectangleUpper,
    add_zero, show (980 : ℝ) / 1600 = 49 / 80 by norm_num,
    show ((980 : ℝ) + 20) / 1600 = (49 + 1) / 80 by norm_num] using h

theorem hpThetaJensenEighthBatch050_integral_bounds :
    hpThetaJensenEighthRectangleLower 50 ≤
        (∫ u : ℝ in Set.Ioo (50 / 80 : ℝ) ((50 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (50 / 80 : ℝ) ((50 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenEighthRectangleUpper 50 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch050Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch050Lower]
  have h := hpThetaJensen_eighthBatchIntegral_of_kernelBounds (1000 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch050Lower hpThetaJensenCellsBatch050Upper hL
    hpThetaJensenCellsBatch050_bounds
  simpa only [hpThetaJensenEighthRectangleLower, hpThetaJensenEighthRectangleUpper,
    add_zero, show (1000 : ℝ) / 1600 = 50 / 80 by norm_num,
    show ((1000 : ℝ) + 20) / 1600 = (50 + 1) / 80 by norm_num] using h

theorem hpThetaJensenEighthBatch051_integral_bounds :
    hpThetaJensenEighthRectangleLower 51 ≤
        (∫ u : ℝ in Set.Ioo (51 / 80 : ℝ) ((51 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (51 / 80 : ℝ) ((51 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenEighthRectangleUpper 51 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch051Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch051Lower]
  have h := hpThetaJensen_eighthBatchIntegral_of_kernelBounds (1020 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch051Lower hpThetaJensenCellsBatch051Upper hL
    hpThetaJensenCellsBatch051_bounds
  simpa only [hpThetaJensenEighthRectangleLower, hpThetaJensenEighthRectangleUpper,
    add_zero, show (1020 : ℝ) / 1600 = 51 / 80 by norm_num,
    show ((1020 : ℝ) + 20) / 1600 = (51 + 1) / 80 by norm_num] using h

theorem hpThetaJensenEighthBatch052_integral_bounds :
    hpThetaJensenEighthRectangleLower 52 ≤
        (∫ u : ℝ in Set.Ioo (52 / 80 : ℝ) ((52 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (52 / 80 : ℝ) ((52 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenEighthRectangleUpper 52 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch052Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch052Lower]
  have h := hpThetaJensen_eighthBatchIntegral_of_kernelBounds (1040 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch052Lower hpThetaJensenCellsBatch052Upper hL
    hpThetaJensenCellsBatch052_bounds
  simpa only [hpThetaJensenEighthRectangleLower, hpThetaJensenEighthRectangleUpper,
    add_zero, show (1040 : ℝ) / 1600 = 52 / 80 by norm_num,
    show ((1040 : ℝ) + 20) / 1600 = (52 + 1) / 80 by norm_num] using h

theorem hpThetaJensenEighthBatch053_integral_bounds :
    hpThetaJensenEighthRectangleLower 53 ≤
        (∫ u : ℝ in Set.Ioo (53 / 80 : ℝ) ((53 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (53 / 80 : ℝ) ((53 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenEighthRectangleUpper 53 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch053Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch053Lower]
  have h := hpThetaJensen_eighthBatchIntegral_of_kernelBounds (1060 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch053Lower hpThetaJensenCellsBatch053Upper hL
    hpThetaJensenCellsBatch053_bounds
  simpa only [hpThetaJensenEighthRectangleLower, hpThetaJensenEighthRectangleUpper,
    add_zero, show (1060 : ℝ) / 1600 = 53 / 80 by norm_num,
    show ((1060 : ℝ) + 20) / 1600 = (53 + 1) / 80 by norm_num] using h

theorem hpThetaJensenEighthBatch054_integral_bounds :
    hpThetaJensenEighthRectangleLower 54 ≤
        (∫ u : ℝ in Set.Ioo (54 / 80 : ℝ) ((54 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (54 / 80 : ℝ) ((54 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenEighthRectangleUpper 54 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch054Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch054Lower]
  have h := hpThetaJensen_eighthBatchIntegral_of_kernelBounds (1080 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch054Lower hpThetaJensenCellsBatch054Upper hL
    hpThetaJensenCellsBatch054_bounds
  simpa only [hpThetaJensenEighthRectangleLower, hpThetaJensenEighthRectangleUpper,
    add_zero, show (1080 : ℝ) / 1600 = 54 / 80 by norm_num,
    show ((1080 : ℝ) + 20) / 1600 = (54 + 1) / 80 by norm_num] using h

theorem hpThetaJensenEighthBatch055_integral_bounds :
    hpThetaJensenEighthRectangleLower 55 ≤
        (∫ u : ℝ in Set.Ioo (55 / 80 : ℝ) ((55 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (55 / 80 : ℝ) ((55 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenEighthRectangleUpper 55 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch055Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch055Lower]
  have h := hpThetaJensen_eighthBatchIntegral_of_kernelBounds (1100 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch055Lower hpThetaJensenCellsBatch055Upper hL
    hpThetaJensenCellsBatch055_bounds
  simpa only [hpThetaJensenEighthRectangleLower, hpThetaJensenEighthRectangleUpper,
    add_zero, show (1100 : ℝ) / 1600 = 55 / 80 by norm_num,
    show ((1100 : ℝ) + 20) / 1600 = (55 + 1) / 80 by norm_num] using h

theorem hpThetaJensenEighthBatch056_integral_bounds :
    hpThetaJensenEighthRectangleLower 56 ≤
        (∫ u : ℝ in Set.Ioo (56 / 80 : ℝ) ((56 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (56 / 80 : ℝ) ((56 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenEighthRectangleUpper 56 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch056Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch056Lower]
  have h := hpThetaJensen_eighthBatchIntegral_of_kernelBounds (1120 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch056Lower hpThetaJensenCellsBatch056Upper hL
    hpThetaJensenCellsBatch056_bounds
  simpa only [hpThetaJensenEighthRectangleLower, hpThetaJensenEighthRectangleUpper,
    add_zero, show (1120 : ℝ) / 1600 = 56 / 80 by norm_num,
    show ((1120 : ℝ) + 20) / 1600 = (56 + 1) / 80 by norm_num] using h

theorem hpThetaJensenEighthBatch057_integral_bounds :
    hpThetaJensenEighthRectangleLower 57 ≤
        (∫ u : ℝ in Set.Ioo (57 / 80 : ℝ) ((57 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (57 / 80 : ℝ) ((57 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenEighthRectangleUpper 57 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch057Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch057Lower]
  have h := hpThetaJensen_eighthBatchIntegral_of_kernelBounds (1140 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch057Lower hpThetaJensenCellsBatch057Upper hL
    hpThetaJensenCellsBatch057_bounds
  simpa only [hpThetaJensenEighthRectangleLower, hpThetaJensenEighthRectangleUpper,
    add_zero, show (1140 : ℝ) / 1600 = 57 / 80 by norm_num,
    show ((1140 : ℝ) + 20) / 1600 = (57 + 1) / 80 by norm_num] using h

theorem hpThetaJensenEighthBatch058_integral_bounds :
    hpThetaJensenEighthRectangleLower 58 ≤
        (∫ u : ℝ in Set.Ioo (58 / 80 : ℝ) ((58 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (58 / 80 : ℝ) ((58 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenEighthRectangleUpper 58 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch058Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch058Lower]
  have h := hpThetaJensen_eighthBatchIntegral_of_kernelBounds (1160 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch058Lower hpThetaJensenCellsBatch058Upper hL
    hpThetaJensenCellsBatch058_bounds
  simpa only [hpThetaJensenEighthRectangleLower, hpThetaJensenEighthRectangleUpper,
    add_zero, show (1160 : ℝ) / 1600 = 58 / 80 by norm_num,
    show ((1160 : ℝ) + 20) / 1600 = (58 + 1) / 80 by norm_num] using h

theorem hpThetaJensenEighthBatch059_integral_bounds :
    hpThetaJensenEighthRectangleLower 59 ≤
        (∫ u : ℝ in Set.Ioo (59 / 80 : ℝ) ((59 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (59 / 80 : ℝ) ((59 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenEighthRectangleUpper 59 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch059Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch059Lower]
  have h := hpThetaJensen_eighthBatchIntegral_of_kernelBounds (1180 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch059Lower hpThetaJensenCellsBatch059Upper hL
    hpThetaJensenCellsBatch059_bounds
  simpa only [hpThetaJensenEighthRectangleLower, hpThetaJensenEighthRectangleUpper,
    add_zero, show (1180 : ℝ) / 1600 = 59 / 80 by norm_num,
    show ((1180 : ℝ) + 20) / 1600 = (59 + 1) / 80 by norm_num] using h

theorem hpThetaJensenEighthBatch060_integral_bounds :
    hpThetaJensenEighthRectangleLower 60 ≤
        (∫ u : ℝ in Set.Ioo (60 / 80 : ℝ) ((60 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (60 / 80 : ℝ) ((60 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenEighthRectangleUpper 60 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch060Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch060Lower]
  have h := hpThetaJensen_eighthBatchIntegral_of_kernelBounds (1200 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch060Lower hpThetaJensenCellsBatch060Upper hL
    hpThetaJensenCellsBatch060_bounds
  simpa only [hpThetaJensenEighthRectangleLower, hpThetaJensenEighthRectangleUpper,
    add_zero, show (1200 : ℝ) / 1600 = 60 / 80 by norm_num,
    show ((1200 : ℝ) + 20) / 1600 = (60 + 1) / 80 by norm_num] using h

theorem hpThetaJensenEighthBatch061_integral_bounds :
    hpThetaJensenEighthRectangleLower 61 ≤
        (∫ u : ℝ in Set.Ioo (61 / 80 : ℝ) ((61 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (61 / 80 : ℝ) ((61 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenEighthRectangleUpper 61 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch061Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch061Lower]
  have h := hpThetaJensen_eighthBatchIntegral_of_kernelBounds (1220 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch061Lower hpThetaJensenCellsBatch061Upper hL
    hpThetaJensenCellsBatch061_bounds
  simpa only [hpThetaJensenEighthRectangleLower, hpThetaJensenEighthRectangleUpper,
    add_zero, show (1220 : ℝ) / 1600 = 61 / 80 by norm_num,
    show ((1220 : ℝ) + 20) / 1600 = (61 + 1) / 80 by norm_num] using h

theorem hpThetaJensenEighthBatch062_integral_bounds :
    hpThetaJensenEighthRectangleLower 62 ≤
        (∫ u : ℝ in Set.Ioo (62 / 80 : ℝ) ((62 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (62 / 80 : ℝ) ((62 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenEighthRectangleUpper 62 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch062Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch062Lower]
  have h := hpThetaJensen_eighthBatchIntegral_of_kernelBounds (1240 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch062Lower hpThetaJensenCellsBatch062Upper hL
    hpThetaJensenCellsBatch062_bounds
  simpa only [hpThetaJensenEighthRectangleLower, hpThetaJensenEighthRectangleUpper,
    add_zero, show (1240 : ℝ) / 1600 = 62 / 80 by norm_num,
    show ((1240 : ℝ) + 20) / 1600 = (62 + 1) / 80 by norm_num] using h

theorem hpThetaJensenEighthBatch063_integral_bounds :
    hpThetaJensenEighthRectangleLower 63 ≤
        (∫ u : ℝ in Set.Ioo (63 / 80 : ℝ) ((63 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (63 / 80 : ℝ) ((63 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenEighthRectangleUpper 63 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch063Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch063Lower]
  have h := hpThetaJensen_eighthBatchIntegral_of_kernelBounds (1260 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch063Lower hpThetaJensenCellsBatch063Upper hL
    hpThetaJensenCellsBatch063_bounds
  simpa only [hpThetaJensenEighthRectangleLower, hpThetaJensenEighthRectangleUpper,
    add_zero, show (1260 : ℝ) / 1600 = 63 / 80 by norm_num,
    show ((1260 : ℝ) + 20) / 1600 = (63 + 1) / 80 by norm_num] using h

theorem hpThetaJensenEighthBatch064_integral_bounds :
    hpThetaJensenEighthRectangleLower 64 ≤
        (∫ u : ℝ in Set.Ioo (64 / 80 : ℝ) ((64 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (64 / 80 : ℝ) ((64 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenEighthRectangleUpper 64 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch064Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch064Lower]
  have h := hpThetaJensen_eighthBatchIntegral_of_kernelBounds (1280 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch064Lower hpThetaJensenCellsBatch064Upper hL
    hpThetaJensenCellsBatch064_bounds
  simpa only [hpThetaJensenEighthRectangleLower, hpThetaJensenEighthRectangleUpper,
    add_zero, show (1280 : ℝ) / 1600 = 64 / 80 by norm_num,
    show ((1280 : ℝ) + 20) / 1600 = (64 + 1) / 80 by norm_num] using h

theorem hpThetaJensenEighthBatch065_integral_bounds :
    hpThetaJensenEighthRectangleLower 65 ≤
        (∫ u : ℝ in Set.Ioo (65 / 80 : ℝ) ((65 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (65 / 80 : ℝ) ((65 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenEighthRectangleUpper 65 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch065Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch065Lower]
  have h := hpThetaJensen_eighthBatchIntegral_of_kernelBounds (1300 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch065Lower hpThetaJensenCellsBatch065Upper hL
    hpThetaJensenCellsBatch065_bounds
  simpa only [hpThetaJensenEighthRectangleLower, hpThetaJensenEighthRectangleUpper,
    add_zero, show (1300 : ℝ) / 1600 = 65 / 80 by norm_num,
    show ((1300 : ℝ) + 20) / 1600 = (65 + 1) / 80 by norm_num] using h

theorem hpThetaJensenEighthBatch066_integral_bounds :
    hpThetaJensenEighthRectangleLower 66 ≤
        (∫ u : ℝ in Set.Ioo (66 / 80 : ℝ) ((66 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (66 / 80 : ℝ) ((66 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenEighthRectangleUpper 66 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch066Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch066Lower]
  have h := hpThetaJensen_eighthBatchIntegral_of_kernelBounds (1320 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch066Lower hpThetaJensenCellsBatch066Upper hL
    hpThetaJensenCellsBatch066_bounds
  simpa only [hpThetaJensenEighthRectangleLower, hpThetaJensenEighthRectangleUpper,
    add_zero, show (1320 : ℝ) / 1600 = 66 / 80 by norm_num,
    show ((1320 : ℝ) + 20) / 1600 = (66 + 1) / 80 by norm_num] using h

theorem hpThetaJensenEighthBatch067_integral_bounds :
    hpThetaJensenEighthRectangleLower 67 ≤
        (∫ u : ℝ in Set.Ioo (67 / 80 : ℝ) ((67 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (67 / 80 : ℝ) ((67 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenEighthRectangleUpper 67 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch067Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch067Lower]
  have h := hpThetaJensen_eighthBatchIntegral_of_kernelBounds (1340 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch067Lower hpThetaJensenCellsBatch067Upper hL
    hpThetaJensenCellsBatch067_bounds
  simpa only [hpThetaJensenEighthRectangleLower, hpThetaJensenEighthRectangleUpper,
    add_zero, show (1340 : ℝ) / 1600 = 67 / 80 by norm_num,
    show ((1340 : ℝ) + 20) / 1600 = (67 + 1) / 80 by norm_num] using h

theorem hpThetaJensenEighthBatch068_integral_bounds :
    hpThetaJensenEighthRectangleLower 68 ≤
        (∫ u : ℝ in Set.Ioo (68 / 80 : ℝ) ((68 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (68 / 80 : ℝ) ((68 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenEighthRectangleUpper 68 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch068Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch068Lower]
  have h := hpThetaJensen_eighthBatchIntegral_of_kernelBounds (1360 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch068Lower hpThetaJensenCellsBatch068Upper hL
    hpThetaJensenCellsBatch068_bounds
  simpa only [hpThetaJensenEighthRectangleLower, hpThetaJensenEighthRectangleUpper,
    add_zero, show (1360 : ℝ) / 1600 = 68 / 80 by norm_num,
    show ((1360 : ℝ) + 20) / 1600 = (68 + 1) / 80 by norm_num] using h

theorem hpThetaJensenEighthBatch069_integral_bounds :
    hpThetaJensenEighthRectangleLower 69 ≤
        (∫ u : ℝ in Set.Ioo (69 / 80 : ℝ) ((69 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (69 / 80 : ℝ) ((69 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenEighthRectangleUpper 69 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch069Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch069Lower]
  have h := hpThetaJensen_eighthBatchIntegral_of_kernelBounds (1380 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch069Lower hpThetaJensenCellsBatch069Upper hL
    hpThetaJensenCellsBatch069_bounds
  simpa only [hpThetaJensenEighthRectangleLower, hpThetaJensenEighthRectangleUpper,
    add_zero, show (1380 : ℝ) / 1600 = 69 / 80 by norm_num,
    show ((1380 : ℝ) + 20) / 1600 = (69 + 1) / 80 by norm_num] using h

theorem hpThetaJensenEighthBatch070_integral_bounds :
    hpThetaJensenEighthRectangleLower 70 ≤
        (∫ u : ℝ in Set.Ioo (70 / 80 : ℝ) ((70 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (70 / 80 : ℝ) ((70 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenEighthRectangleUpper 70 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch070Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch070Lower]
  have h := hpThetaJensen_eighthBatchIntegral_of_kernelBounds (1400 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch070Lower hpThetaJensenCellsBatch070Upper hL
    hpThetaJensenCellsBatch070_bounds
  simpa only [hpThetaJensenEighthRectangleLower, hpThetaJensenEighthRectangleUpper,
    add_zero, show (1400 : ℝ) / 1600 = 70 / 80 by norm_num,
    show ((1400 : ℝ) + 20) / 1600 = (70 + 1) / 80 by norm_num] using h

theorem hpThetaJensenEighthBatch071_integral_bounds :
    hpThetaJensenEighthRectangleLower 71 ≤
        (∫ u : ℝ in Set.Ioo (71 / 80 : ℝ) ((71 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (71 / 80 : ℝ) ((71 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenEighthRectangleUpper 71 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch071Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch071Lower]
  have h := hpThetaJensen_eighthBatchIntegral_of_kernelBounds (1420 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch071Lower hpThetaJensenCellsBatch071Upper hL
    hpThetaJensenCellsBatch071_bounds
  simpa only [hpThetaJensenEighthRectangleLower, hpThetaJensenEighthRectangleUpper,
    add_zero, show (1420 : ℝ) / 1600 = 71 / 80 by norm_num,
    show ((1420 : ℝ) + 20) / 1600 = (71 + 1) / 80 by norm_num] using h

theorem hpThetaJensenEighthBatch072_integral_bounds :
    hpThetaJensenEighthRectangleLower 72 ≤
        (∫ u : ℝ in Set.Ioo (72 / 80 : ℝ) ((72 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (72 / 80 : ℝ) ((72 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenEighthRectangleUpper 72 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch072Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch072Lower]
  have h := hpThetaJensen_eighthBatchIntegral_of_kernelBounds (1440 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch072Lower hpThetaJensenCellsBatch072Upper hL
    hpThetaJensenCellsBatch072_bounds
  simpa only [hpThetaJensenEighthRectangleLower, hpThetaJensenEighthRectangleUpper,
    add_zero, show (1440 : ℝ) / 1600 = 72 / 80 by norm_num,
    show ((1440 : ℝ) + 20) / 1600 = (72 + 1) / 80 by norm_num] using h

theorem hpThetaJensenEighthBatch073_integral_bounds :
    hpThetaJensenEighthRectangleLower 73 ≤
        (∫ u : ℝ in Set.Ioo (73 / 80 : ℝ) ((73 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (73 / 80 : ℝ) ((73 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenEighthRectangleUpper 73 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch073Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch073Lower]
  have h := hpThetaJensen_eighthBatchIntegral_of_kernelBounds (1460 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch073Lower hpThetaJensenCellsBatch073Upper hL
    hpThetaJensenCellsBatch073_bounds
  simpa only [hpThetaJensenEighthRectangleLower, hpThetaJensenEighthRectangleUpper,
    add_zero, show (1460 : ℝ) / 1600 = 73 / 80 by norm_num,
    show ((1460 : ℝ) + 20) / 1600 = (73 + 1) / 80 by norm_num] using h

theorem hpThetaJensenEighthBatch074_integral_bounds :
    hpThetaJensenEighthRectangleLower 74 ≤
        (∫ u : ℝ in Set.Ioo (74 / 80 : ℝ) ((74 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (74 / 80 : ℝ) ((74 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenEighthRectangleUpper 74 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch074Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch074Lower]
  have h := hpThetaJensen_eighthBatchIntegral_of_kernelBounds (1480 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch074Lower hpThetaJensenCellsBatch074Upper hL
    hpThetaJensenCellsBatch074_bounds
  simpa only [hpThetaJensenEighthRectangleLower, hpThetaJensenEighthRectangleUpper,
    add_zero, show (1480 : ℝ) / 1600 = 74 / 80 by norm_num,
    show ((1480 : ℝ) + 20) / 1600 = (74 + 1) / 80 by norm_num] using h

theorem hpThetaJensenEighthBatch075_integral_bounds :
    hpThetaJensenEighthRectangleLower 75 ≤
        (∫ u : ℝ in Set.Ioo (75 / 80 : ℝ) ((75 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (75 / 80 : ℝ) ((75 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenEighthRectangleUpper 75 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch075Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch075Lower]
  have h := hpThetaJensen_eighthBatchIntegral_of_kernelBounds (1500 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch075Lower hpThetaJensenCellsBatch075Upper hL
    hpThetaJensenCellsBatch075_bounds
  simpa only [hpThetaJensenEighthRectangleLower, hpThetaJensenEighthRectangleUpper,
    add_zero, show (1500 : ℝ) / 1600 = 75 / 80 by norm_num,
    show ((1500 : ℝ) + 20) / 1600 = (75 + 1) / 80 by norm_num] using h

theorem hpThetaJensenEighthBatch076_integral_bounds :
    hpThetaJensenEighthRectangleLower 76 ≤
        (∫ u : ℝ in Set.Ioo (76 / 80 : ℝ) ((76 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (76 / 80 : ℝ) ((76 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenEighthRectangleUpper 76 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch076Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch076Lower]
  have h := hpThetaJensen_eighthBatchIntegral_of_kernelBounds (1520 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch076Lower hpThetaJensenCellsBatch076Upper hL
    hpThetaJensenCellsBatch076_bounds
  simpa only [hpThetaJensenEighthRectangleLower, hpThetaJensenEighthRectangleUpper,
    add_zero, show (1520 : ℝ) / 1600 = 76 / 80 by norm_num,
    show ((1520 : ℝ) + 20) / 1600 = (76 + 1) / 80 by norm_num] using h

theorem hpThetaJensenEighthBatch077_integral_bounds :
    hpThetaJensenEighthRectangleLower 77 ≤
        (∫ u : ℝ in Set.Ioo (77 / 80 : ℝ) ((77 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (77 / 80 : ℝ) ((77 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenEighthRectangleUpper 77 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch077Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch077Lower]
  have h := hpThetaJensen_eighthBatchIntegral_of_kernelBounds (1540 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch077Lower hpThetaJensenCellsBatch077Upper hL
    hpThetaJensenCellsBatch077_bounds
  simpa only [hpThetaJensenEighthRectangleLower, hpThetaJensenEighthRectangleUpper,
    add_zero, show (1540 : ℝ) / 1600 = 77 / 80 by norm_num,
    show ((1540 : ℝ) + 20) / 1600 = (77 + 1) / 80 by norm_num] using h

theorem hpThetaJensenEighthBatch078_integral_bounds :
    hpThetaJensenEighthRectangleLower 78 ≤
        (∫ u : ℝ in Set.Ioo (78 / 80 : ℝ) ((78 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (78 / 80 : ℝ) ((78 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenEighthRectangleUpper 78 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch078Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch078Lower]
  have h := hpThetaJensen_eighthBatchIntegral_of_kernelBounds (1560 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch078Lower hpThetaJensenCellsBatch078Upper hL
    hpThetaJensenCellsBatch078_bounds
  simpa only [hpThetaJensenEighthRectangleLower, hpThetaJensenEighthRectangleUpper,
    add_zero, show (1560 : ℝ) / 1600 = 78 / 80 by norm_num,
    show ((1560 : ℝ) + 20) / 1600 = (78 + 1) / 80 by norm_num] using h

theorem hpThetaJensenEighthBatch079_integral_bounds :
    hpThetaJensenEighthRectangleLower 79 ≤
        (∫ u : ℝ in Set.Ioo (79 / 80 : ℝ) ((79 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (79 / 80 : ℝ) ((79 + 1) / 80 : ℝ),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenEighthRectangleUpper 79 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch079Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch079Lower]
  have h := hpThetaJensen_eighthBatchIntegral_of_kernelBounds (1580 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch079Lower hpThetaJensenCellsBatch079Upper hL
    hpThetaJensenCellsBatch079_bounds
  simpa only [hpThetaJensenEighthRectangleLower, hpThetaJensenEighthRectangleUpper,
    add_zero, show (1580 : ℝ) / 1600 = 79 / 80 by norm_num,
    show ((1580 : ℝ) + 20) / 1600 = (79 + 1) / 80 by norm_num] using h

theorem hpThetaJensen_eighthBatchIntegral_bounds (b : Fin 80) :
    hpThetaJensenEighthRectangleLower b.val ≤
        (∫ u : ℝ in Set.Ioo ((b.val : ℝ) / 80) (((b.val : ℝ) + 1) / 80),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo ((b.val : ℝ) / 80) (((b.val : ℝ) + 1) / 80),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenEighthRectangleUpper b.val := by
  fin_cases b
  · simpa using hpThetaJensenEighthBatch000_integral_bounds
  · simpa using hpThetaJensenEighthBatch001_integral_bounds
  · exact hpThetaJensenEighthBatch002_integral_bounds
  · exact hpThetaJensenEighthBatch003_integral_bounds
  · exact hpThetaJensenEighthBatch004_integral_bounds
  · exact hpThetaJensenEighthBatch005_integral_bounds
  · exact hpThetaJensenEighthBatch006_integral_bounds
  · exact hpThetaJensenEighthBatch007_integral_bounds
  · exact hpThetaJensenEighthBatch008_integral_bounds
  · exact hpThetaJensenEighthBatch009_integral_bounds
  · exact hpThetaJensenEighthBatch010_integral_bounds
  · exact hpThetaJensenEighthBatch011_integral_bounds
  · exact hpThetaJensenEighthBatch012_integral_bounds
  · exact hpThetaJensenEighthBatch013_integral_bounds
  · exact hpThetaJensenEighthBatch014_integral_bounds
  · exact hpThetaJensenEighthBatch015_integral_bounds
  · exact hpThetaJensenEighthBatch016_integral_bounds
  · exact hpThetaJensenEighthBatch017_integral_bounds
  · exact hpThetaJensenEighthBatch018_integral_bounds
  · exact hpThetaJensenEighthBatch019_integral_bounds
  · exact hpThetaJensenEighthBatch020_integral_bounds
  · exact hpThetaJensenEighthBatch021_integral_bounds
  · exact hpThetaJensenEighthBatch022_integral_bounds
  · exact hpThetaJensenEighthBatch023_integral_bounds
  · exact hpThetaJensenEighthBatch024_integral_bounds
  · exact hpThetaJensenEighthBatch025_integral_bounds
  · exact hpThetaJensenEighthBatch026_integral_bounds
  · exact hpThetaJensenEighthBatch027_integral_bounds
  · exact hpThetaJensenEighthBatch028_integral_bounds
  · exact hpThetaJensenEighthBatch029_integral_bounds
  · exact hpThetaJensenEighthBatch030_integral_bounds
  · exact hpThetaJensenEighthBatch031_integral_bounds
  · exact hpThetaJensenEighthBatch032_integral_bounds
  · exact hpThetaJensenEighthBatch033_integral_bounds
  · exact hpThetaJensenEighthBatch034_integral_bounds
  · exact hpThetaJensenEighthBatch035_integral_bounds
  · exact hpThetaJensenEighthBatch036_integral_bounds
  · exact hpThetaJensenEighthBatch037_integral_bounds
  · exact hpThetaJensenEighthBatch038_integral_bounds
  · exact hpThetaJensenEighthBatch039_integral_bounds
  · exact hpThetaJensenEighthBatch040_integral_bounds
  · exact hpThetaJensenEighthBatch041_integral_bounds
  · exact hpThetaJensenEighthBatch042_integral_bounds
  · exact hpThetaJensenEighthBatch043_integral_bounds
  · exact hpThetaJensenEighthBatch044_integral_bounds
  · exact hpThetaJensenEighthBatch045_integral_bounds
  · exact hpThetaJensenEighthBatch046_integral_bounds
  · exact hpThetaJensenEighthBatch047_integral_bounds
  · exact hpThetaJensenEighthBatch048_integral_bounds
  · exact hpThetaJensenEighthBatch049_integral_bounds
  · exact hpThetaJensenEighthBatch050_integral_bounds
  · exact hpThetaJensenEighthBatch051_integral_bounds
  · exact hpThetaJensenEighthBatch052_integral_bounds
  · exact hpThetaJensenEighthBatch053_integral_bounds
  · exact hpThetaJensenEighthBatch054_integral_bounds
  · exact hpThetaJensenEighthBatch055_integral_bounds
  · exact hpThetaJensenEighthBatch056_integral_bounds
  · exact hpThetaJensenEighthBatch057_integral_bounds
  · exact hpThetaJensenEighthBatch058_integral_bounds
  · exact hpThetaJensenEighthBatch059_integral_bounds
  · exact hpThetaJensenEighthBatch060_integral_bounds
  · exact hpThetaJensenEighthBatch061_integral_bounds
  · exact hpThetaJensenEighthBatch062_integral_bounds
  · exact hpThetaJensenEighthBatch063_integral_bounds
  · exact hpThetaJensenEighthBatch064_integral_bounds
  · exact hpThetaJensenEighthBatch065_integral_bounds
  · exact hpThetaJensenEighthBatch066_integral_bounds
  · exact hpThetaJensenEighthBatch067_integral_bounds
  · exact hpThetaJensenEighthBatch068_integral_bounds
  · exact hpThetaJensenEighthBatch069_integral_bounds
  · exact hpThetaJensenEighthBatch070_integral_bounds
  · exact hpThetaJensenEighthBatch071_integral_bounds
  · exact hpThetaJensenEighthBatch072_integral_bounds
  · exact hpThetaJensenEighthBatch073_integral_bounds
  · exact hpThetaJensenEighthBatch074_integral_bounds
  · exact hpThetaJensenEighthBatch075_integral_bounds
  · exact hpThetaJensenEighthBatch076_integral_bounds
  · exact hpThetaJensenEighthBatch077_integral_bounds
  · exact hpThetaJensenEighthBatch078_integral_bounds
  · exact hpThetaJensenEighthBatch079_integral_bounds

theorem hpThetaJensen_eighthFiniteIntegral_bounds :
    (158 / 1000000 : ℝ) ≤
        (∫ u : ℝ in Set.Ioo 0 1, u ^ 8 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo 0 1, u ^ 8 * hpRiemannThetaDifferentialKernel u) ≤
        (164 / 1000000 : ℝ) - 1 / 50000000 := by
  have hlow :
      (∑ b ∈ Finset.range 80, hpThetaJensenEighthRectangleLower b) ≤
      ∑ b ∈ Finset.range 80,
        ∫ u : ℝ in Set.Ioo ((b : ℝ) / 80) (((b : ℝ) + 1) / 80),
          u ^ 8 * hpRiemannThetaDifferentialKernel u := by
    apply Finset.sum_le_sum
    intro b hb
    exact (hpThetaJensen_eighthBatchIntegral_bounds
      ⟨b, Finset.mem_range.mp hb⟩).1
  have hupp :
      (∑ b ∈ Finset.range 80,
        ∫ u : ℝ in Set.Ioo ((b : ℝ) / 80) (((b : ℝ) + 1) / 80),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) ≤
      ∑ b ∈ Finset.range 80, hpThetaJensenEighthRectangleUpper b := by
    apply Finset.sum_le_sum
    intro b hb
    exact (hpThetaJensen_eighthBatchIntegral_bounds
      ⟨b, Finset.mem_range.mp hb⟩).2
  have hsum :
      (∑ b ∈ Finset.range 80,
        ∫ u : ℝ in Set.Ioo ((b : ℝ) / 80) (((b : ℝ) + 1) / 80),
          u ^ 8 * hpRiemannThetaDifferentialKernel u) =
      ∫ u : ℝ in Set.Ioo 0 1, u ^ 8 * hpRiemannThetaDifferentialKernel u := by
    have h := hpThetaJensen_natPowerUniformCellIntegral_sum 8 80 0
      (1 / 80) (by norm_num) (by norm_num)
    simpa only [zero_add, mul_one_div, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat,
      show (80 : ℝ) / 80 = 1 by norm_num] using h
  rw [hsum] at hlow hupp
  exact ⟨le_trans hpThetaJensen_eighthRectangle_lower_numeric hlow,
    le_trans hupp hpThetaJensen_eighthRectangle_upper_numeric⟩

theorem hpThetaJensen_eighthMoment_integral_split :
    hpThetaPhiEvenMoment 4 =
      (∫ u : ℝ in Set.Ioo 0 1, u ^ 8 * hpRiemannThetaDifferentialKernel u) +
      (∫ u : ℝ in Set.Ioi 1, u ^ 8 * hpRiemannThetaDifferentialKernel u) := by
  have h := intervalIntegral.integral_Ioi_sub_Ioi
    hpThetaPhi_eighthMoment_integrableOn (show (0 : ℝ) ≤ 1 by norm_num)
  rw [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num),
    integral_Ioc_eq_integral_Ioo] at h
  change (∫ u : ℝ in Set.Ioi 0, u ^ 8 * hpRiemannThetaDifferentialKernel u) = _
  linarith

theorem hpThetaJensen_eighthMoment_ge_certified :
    (158 / 1000000 : ℝ) ≤ hpThetaPhiEvenMoment 4 := by
  have hfin := hpThetaJensen_eighthFiniteIntegral_bounds.1
  have htail :
      0 ≤ ∫ u : ℝ in Set.Ioi 1, u ^ 8 * hpRiemannThetaDifferentialKernel u := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : 0 ≤ u := by
      change (1 : ℝ) < u at hu
      linarith
    exact mul_nonneg (pow_nonneg hu0 8)
      (le_of_lt (hpThetaPhi_pos_on_nonnegative u hu0))
  have hsplit := hpThetaJensen_eighthMoment_integral_split
  linarith

theorem hpThetaJensen_eighthMoment_le_certified :
    hpThetaPhiEvenMoment 4 ≤ (164 / 1000000 : ℝ) := by
  have hfin := hpThetaJensen_eighthFiniteIntegral_bounds.2
  have htail := hpThetaJensen_eighthMoment_tail_le_twoEminusEight
  have hsplit := hpThetaJensen_eighthMoment_integral_split
  linarith

theorem hpThetaJensen_eighthMoment_certified_bounds :
    (158 / 1000000 : ℝ) ≤ hpThetaPhiEvenMoment 4 ∧
      hpThetaPhiEvenMoment 4 ≤ (164 / 1000000 : ℝ) :=
  ⟨hpThetaJensen_eighthMoment_ge_certified, hpThetaJensen_eighthMoment_le_certified⟩

#print axioms hpThetaJensen_eighthBatchIntegral_of_kernelBounds
#print axioms hpThetaJensen_eighthBatchIntegral_bounds
#print axioms hpThetaJensen_eighthFiniteIntegral_bounds
#print axioms hpThetaJensen_eighthMoment_integral_split
#print axioms hpThetaJensen_eighthMoment_ge_certified
#print axioms hpThetaJensen_eighthMoment_le_certified
#print axioms hpThetaJensen_eighthMoment_certified_bounds
end HodgeProofHP
