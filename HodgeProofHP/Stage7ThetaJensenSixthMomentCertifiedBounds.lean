/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenSixthMomentRectangles
import HodgeProofHP.Stage7ThetaJensenSixthMomentCellBounds
import HodgeProofHP.Stage7ThetaJensenSixthMomentTailBounds

/-!
# Full certified sixth-moment bounds

Integrate the existing rational rectangles on (0,1) and add the analytic
tail. No higher-degree root hypothesis is used.
-/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

theorem hpThetaJensen_sixthBatchIntegral_of_kernelBounds
    (s : ℝ) (hs : 0 ≤ s) (L U : ℕ → ℝ)
    (hL : ∀ j : Fin 20, 0 ≤ L j.val)
    (hbound : ∀ (j : Fin 20) (u : ℝ),
      u ∈ Set.Icc ((s + (j.val : ℝ)) / 1600)
        ((s + (j.val : ℝ) + 1) / 1600) →
      L j.val ≤ hpRiemannThetaDifferentialKernel u ∧
        hpRiemannThetaDifferentialKernel u ≤ U j.val) :
    (∑ j ∈ Finset.range 20, ((s + (j : ℝ)) / 1600) ^ 6 * L j / 1600) ≤
        (∫ u : ℝ in Set.Ioo (s / 1600) ((s + 20) / 1600),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (s / 1600) ((s + 20) / 1600),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ≤
        ∑ j ∈ Finset.range 20, ((s + (j : ℝ) + 1) / 1600) ^ 6 * U j / 1600 := by
  have hcell (j : Fin 20) :
      ((s + (j.val : ℝ)) / 1600) ^ 6 * L j.val / 1600 ≤
          (∫ u : ℝ in Set.Ioo ((s + (j.val : ℝ)) / 1600)
            ((s + (j.val : ℝ) + 1) / 1600),
            u ^ 6 * hpRiemannThetaDifferentialKernel u) ∧
        (∫ u : ℝ in Set.Ioo ((s + (j.val : ℝ)) / 1600)
            ((s + (j.val : ℝ) + 1) / 1600),
            u ^ 6 * hpRiemannThetaDifferentialKernel u) ≤
          ((s + (j.val : ℝ) + 1) / 1600) ^ 6 * U j.val / 1600 := by
    have hl : 0 ≤ (s + (j.val : ℝ)) / 1600 := by positivity
    have hlr : (s + (j.val : ℝ)) / 1600 ≤
        (s + (j.val : ℝ) + 1) / 1600 := by linarith
    have h := hpThetaJensen_sixthCellIntegral_bounds
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
          u ^ 6 * hpRiemannThetaDifferentialKernel u) =
      ∫ u : ℝ in Set.Ioo (s / 1600) ((s + 20) / 1600),
        u ^ 6 * hpRiemannThetaDifferentialKernel u := by
    have h := hpThetaJensen_natPowerUniformCellIntegral_sum 6 20
      (s / 1600) (1 / 1600) (by positivity) (by norm_num)
    have hc (j : ℕ) :
        Set.Ioo ((s + (j : ℝ)) / 1600) ((s + (j : ℝ) + 1) / 1600) =
        Set.Ioo (s / 1600 + (j : ℝ) * (1 / 1600))
          (s / 1600 + ((j + 1 : ℕ) : ℝ) * (1 / 1600)) := by
      congr 1 <;> push_cast <;> ring
    simp_rw [hc]
    norm_num only [Nat.cast_ofNat] at h
    have hend : s / 1600 + (20 : ℝ) * (1 / 1600) = (s + 20) / 1600 := by ring
    rw [hend] at h
    exact h
  have hlow :
      (∑ j ∈ Finset.range 20, ((s + (j : ℝ)) / 1600) ^ 6 * L j / 1600) ≤
      ∑ j ∈ Finset.range 20,
        ∫ u : ℝ in Set.Ioo ((s + (j : ℝ)) / 1600)
          ((s + (j : ℝ) + 1) / 1600),
          u ^ 6 * hpRiemannThetaDifferentialKernel u := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hcell ⟨j, Finset.mem_range.mp hj⟩).1
  have hupp :
      (∑ j ∈ Finset.range 20,
        ∫ u : ℝ in Set.Ioo ((s + (j : ℝ)) / 1600)
          ((s + (j : ℝ) + 1) / 1600),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, ((s + (j : ℝ) + 1) / 1600) ^ 6 * U j / 1600 := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hcell ⟨j, Finset.mem_range.mp hj⟩).2
  rw [hsum] at hlow hupp
  exact ⟨hlow, hupp⟩


theorem hpThetaJensenSixthBatch000_integral_bounds :
    hpThetaJensenSixthRectangleLower 0 ≤
        (∫ u : ℝ in Set.Ioo (0 / 80 : ℝ) ((0 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (0 / 80 : ℝ) ((0 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenSixthRectangleUpper 0 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch000Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch000Lower]
  have h := hpThetaJensen_sixthBatchIntegral_of_kernelBounds (0 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch000Lower hpThetaJensenCellsBatch000Upper hL
    hpThetaJensenCellsBatch000_bounds
  simpa only [hpThetaJensenSixthRectangleLower, hpThetaJensenSixthRectangleUpper,
    add_zero, show (0 : ℝ) / 1600 = 0 / 80 by norm_num,
    show ((0 : ℝ) + 20) / 1600 = (0 + 1) / 80 by norm_num] using h

theorem hpThetaJensenSixthBatch001_integral_bounds :
    hpThetaJensenSixthRectangleLower 1 ≤
        (∫ u : ℝ in Set.Ioo (1 / 80 : ℝ) ((1 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (1 / 80 : ℝ) ((1 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenSixthRectangleUpper 1 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch001Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch001Lower]
  have h := hpThetaJensen_sixthBatchIntegral_of_kernelBounds (20 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch001Lower hpThetaJensenCellsBatch001Upper hL
    hpThetaJensenCellsBatch001_bounds
  simpa only [hpThetaJensenSixthRectangleLower, hpThetaJensenSixthRectangleUpper,
    add_zero, show (20 : ℝ) / 1600 = 1 / 80 by norm_num,
    show ((20 : ℝ) + 20) / 1600 = (1 + 1) / 80 by norm_num] using h

theorem hpThetaJensenSixthBatch002_integral_bounds :
    hpThetaJensenSixthRectangleLower 2 ≤
        (∫ u : ℝ in Set.Ioo (2 / 80 : ℝ) ((2 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (2 / 80 : ℝ) ((2 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenSixthRectangleUpper 2 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch002Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch002Lower]
  have h := hpThetaJensen_sixthBatchIntegral_of_kernelBounds (40 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch002Lower hpThetaJensenCellsBatch002Upper hL
    hpThetaJensenCellsBatch002_bounds
  simpa only [hpThetaJensenSixthRectangleLower, hpThetaJensenSixthRectangleUpper,
    add_zero, show (40 : ℝ) / 1600 = 2 / 80 by norm_num,
    show ((40 : ℝ) + 20) / 1600 = (2 + 1) / 80 by norm_num] using h

theorem hpThetaJensenSixthBatch003_integral_bounds :
    hpThetaJensenSixthRectangleLower 3 ≤
        (∫ u : ℝ in Set.Ioo (3 / 80 : ℝ) ((3 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (3 / 80 : ℝ) ((3 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenSixthRectangleUpper 3 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch003Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch003Lower]
  have h := hpThetaJensen_sixthBatchIntegral_of_kernelBounds (60 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch003Lower hpThetaJensenCellsBatch003Upper hL
    hpThetaJensenCellsBatch003_bounds
  simpa only [hpThetaJensenSixthRectangleLower, hpThetaJensenSixthRectangleUpper,
    add_zero, show (60 : ℝ) / 1600 = 3 / 80 by norm_num,
    show ((60 : ℝ) + 20) / 1600 = (3 + 1) / 80 by norm_num] using h

theorem hpThetaJensenSixthBatch004_integral_bounds :
    hpThetaJensenSixthRectangleLower 4 ≤
        (∫ u : ℝ in Set.Ioo (4 / 80 : ℝ) ((4 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (4 / 80 : ℝ) ((4 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenSixthRectangleUpper 4 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch004Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch004Lower]
  have h := hpThetaJensen_sixthBatchIntegral_of_kernelBounds (80 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch004Lower hpThetaJensenCellsBatch004Upper hL
    hpThetaJensenCellsBatch004_bounds
  simpa only [hpThetaJensenSixthRectangleLower, hpThetaJensenSixthRectangleUpper,
    add_zero, show (80 : ℝ) / 1600 = 4 / 80 by norm_num,
    show ((80 : ℝ) + 20) / 1600 = (4 + 1) / 80 by norm_num] using h

theorem hpThetaJensenSixthBatch005_integral_bounds :
    hpThetaJensenSixthRectangleLower 5 ≤
        (∫ u : ℝ in Set.Ioo (5 / 80 : ℝ) ((5 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (5 / 80 : ℝ) ((5 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenSixthRectangleUpper 5 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch005Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch005Lower]
  have h := hpThetaJensen_sixthBatchIntegral_of_kernelBounds (100 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch005Lower hpThetaJensenCellsBatch005Upper hL
    hpThetaJensenCellsBatch005_bounds
  simpa only [hpThetaJensenSixthRectangleLower, hpThetaJensenSixthRectangleUpper,
    add_zero, show (100 : ℝ) / 1600 = 5 / 80 by norm_num,
    show ((100 : ℝ) + 20) / 1600 = (5 + 1) / 80 by norm_num] using h

theorem hpThetaJensenSixthBatch006_integral_bounds :
    hpThetaJensenSixthRectangleLower 6 ≤
        (∫ u : ℝ in Set.Ioo (6 / 80 : ℝ) ((6 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (6 / 80 : ℝ) ((6 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenSixthRectangleUpper 6 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch006Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch006Lower]
  have h := hpThetaJensen_sixthBatchIntegral_of_kernelBounds (120 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch006Lower hpThetaJensenCellsBatch006Upper hL
    hpThetaJensenCellsBatch006_bounds
  simpa only [hpThetaJensenSixthRectangleLower, hpThetaJensenSixthRectangleUpper,
    add_zero, show (120 : ℝ) / 1600 = 6 / 80 by norm_num,
    show ((120 : ℝ) + 20) / 1600 = (6 + 1) / 80 by norm_num] using h

theorem hpThetaJensenSixthBatch007_integral_bounds :
    hpThetaJensenSixthRectangleLower 7 ≤
        (∫ u : ℝ in Set.Ioo (7 / 80 : ℝ) ((7 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (7 / 80 : ℝ) ((7 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenSixthRectangleUpper 7 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch007Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch007Lower]
  have h := hpThetaJensen_sixthBatchIntegral_of_kernelBounds (140 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch007Lower hpThetaJensenCellsBatch007Upper hL
    hpThetaJensenCellsBatch007_bounds
  simpa only [hpThetaJensenSixthRectangleLower, hpThetaJensenSixthRectangleUpper,
    add_zero, show (140 : ℝ) / 1600 = 7 / 80 by norm_num,
    show ((140 : ℝ) + 20) / 1600 = (7 + 1) / 80 by norm_num] using h

theorem hpThetaJensenSixthBatch008_integral_bounds :
    hpThetaJensenSixthRectangleLower 8 ≤
        (∫ u : ℝ in Set.Ioo (8 / 80 : ℝ) ((8 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (8 / 80 : ℝ) ((8 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenSixthRectangleUpper 8 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch008Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch008Lower]
  have h := hpThetaJensen_sixthBatchIntegral_of_kernelBounds (160 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch008Lower hpThetaJensenCellsBatch008Upper hL
    hpThetaJensenCellsBatch008_bounds
  simpa only [hpThetaJensenSixthRectangleLower, hpThetaJensenSixthRectangleUpper,
    add_zero, show (160 : ℝ) / 1600 = 8 / 80 by norm_num,
    show ((160 : ℝ) + 20) / 1600 = (8 + 1) / 80 by norm_num] using h

theorem hpThetaJensenSixthBatch009_integral_bounds :
    hpThetaJensenSixthRectangleLower 9 ≤
        (∫ u : ℝ in Set.Ioo (9 / 80 : ℝ) ((9 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (9 / 80 : ℝ) ((9 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenSixthRectangleUpper 9 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch009Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch009Lower]
  have h := hpThetaJensen_sixthBatchIntegral_of_kernelBounds (180 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch009Lower hpThetaJensenCellsBatch009Upper hL
    hpThetaJensenCellsBatch009_bounds
  simpa only [hpThetaJensenSixthRectangleLower, hpThetaJensenSixthRectangleUpper,
    add_zero, show (180 : ℝ) / 1600 = 9 / 80 by norm_num,
    show ((180 : ℝ) + 20) / 1600 = (9 + 1) / 80 by norm_num] using h

theorem hpThetaJensenSixthBatch010_integral_bounds :
    hpThetaJensenSixthRectangleLower 10 ≤
        (∫ u : ℝ in Set.Ioo (10 / 80 : ℝ) ((10 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (10 / 80 : ℝ) ((10 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenSixthRectangleUpper 10 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch010Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch010Lower]
  have h := hpThetaJensen_sixthBatchIntegral_of_kernelBounds (200 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch010Lower hpThetaJensenCellsBatch010Upper hL
    hpThetaJensenCellsBatch010_bounds
  simpa only [hpThetaJensenSixthRectangleLower, hpThetaJensenSixthRectangleUpper,
    add_zero, show (200 : ℝ) / 1600 = 10 / 80 by norm_num,
    show ((200 : ℝ) + 20) / 1600 = (10 + 1) / 80 by norm_num] using h

theorem hpThetaJensenSixthBatch011_integral_bounds :
    hpThetaJensenSixthRectangleLower 11 ≤
        (∫ u : ℝ in Set.Ioo (11 / 80 : ℝ) ((11 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (11 / 80 : ℝ) ((11 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenSixthRectangleUpper 11 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch011Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch011Lower]
  have h := hpThetaJensen_sixthBatchIntegral_of_kernelBounds (220 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch011Lower hpThetaJensenCellsBatch011Upper hL
    hpThetaJensenCellsBatch011_bounds
  simpa only [hpThetaJensenSixthRectangleLower, hpThetaJensenSixthRectangleUpper,
    add_zero, show (220 : ℝ) / 1600 = 11 / 80 by norm_num,
    show ((220 : ℝ) + 20) / 1600 = (11 + 1) / 80 by norm_num] using h

theorem hpThetaJensenSixthBatch012_integral_bounds :
    hpThetaJensenSixthRectangleLower 12 ≤
        (∫ u : ℝ in Set.Ioo (12 / 80 : ℝ) ((12 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (12 / 80 : ℝ) ((12 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenSixthRectangleUpper 12 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch012Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch012Lower]
  have h := hpThetaJensen_sixthBatchIntegral_of_kernelBounds (240 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch012Lower hpThetaJensenCellsBatch012Upper hL
    hpThetaJensenCellsBatch012_bounds
  simpa only [hpThetaJensenSixthRectangleLower, hpThetaJensenSixthRectangleUpper,
    add_zero, show (240 : ℝ) / 1600 = 12 / 80 by norm_num,
    show ((240 : ℝ) + 20) / 1600 = (12 + 1) / 80 by norm_num] using h

theorem hpThetaJensenSixthBatch013_integral_bounds :
    hpThetaJensenSixthRectangleLower 13 ≤
        (∫ u : ℝ in Set.Ioo (13 / 80 : ℝ) ((13 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (13 / 80 : ℝ) ((13 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenSixthRectangleUpper 13 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch013Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch013Lower]
  have h := hpThetaJensen_sixthBatchIntegral_of_kernelBounds (260 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch013Lower hpThetaJensenCellsBatch013Upper hL
    hpThetaJensenCellsBatch013_bounds
  simpa only [hpThetaJensenSixthRectangleLower, hpThetaJensenSixthRectangleUpper,
    add_zero, show (260 : ℝ) / 1600 = 13 / 80 by norm_num,
    show ((260 : ℝ) + 20) / 1600 = (13 + 1) / 80 by norm_num] using h

theorem hpThetaJensenSixthBatch014_integral_bounds :
    hpThetaJensenSixthRectangleLower 14 ≤
        (∫ u : ℝ in Set.Ioo (14 / 80 : ℝ) ((14 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (14 / 80 : ℝ) ((14 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenSixthRectangleUpper 14 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch014Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch014Lower]
  have h := hpThetaJensen_sixthBatchIntegral_of_kernelBounds (280 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch014Lower hpThetaJensenCellsBatch014Upper hL
    hpThetaJensenCellsBatch014_bounds
  simpa only [hpThetaJensenSixthRectangleLower, hpThetaJensenSixthRectangleUpper,
    add_zero, show (280 : ℝ) / 1600 = 14 / 80 by norm_num,
    show ((280 : ℝ) + 20) / 1600 = (14 + 1) / 80 by norm_num] using h

theorem hpThetaJensenSixthBatch015_integral_bounds :
    hpThetaJensenSixthRectangleLower 15 ≤
        (∫ u : ℝ in Set.Ioo (15 / 80 : ℝ) ((15 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (15 / 80 : ℝ) ((15 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenSixthRectangleUpper 15 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch015Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch015Lower]
  have h := hpThetaJensen_sixthBatchIntegral_of_kernelBounds (300 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch015Lower hpThetaJensenCellsBatch015Upper hL
    hpThetaJensenCellsBatch015_bounds
  simpa only [hpThetaJensenSixthRectangleLower, hpThetaJensenSixthRectangleUpper,
    add_zero, show (300 : ℝ) / 1600 = 15 / 80 by norm_num,
    show ((300 : ℝ) + 20) / 1600 = (15 + 1) / 80 by norm_num] using h

theorem hpThetaJensenSixthBatch016_integral_bounds :
    hpThetaJensenSixthRectangleLower 16 ≤
        (∫ u : ℝ in Set.Ioo (16 / 80 : ℝ) ((16 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (16 / 80 : ℝ) ((16 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenSixthRectangleUpper 16 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch016Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch016Lower]
  have h := hpThetaJensen_sixthBatchIntegral_of_kernelBounds (320 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch016Lower hpThetaJensenCellsBatch016Upper hL
    hpThetaJensenCellsBatch016_bounds
  simpa only [hpThetaJensenSixthRectangleLower, hpThetaJensenSixthRectangleUpper,
    add_zero, show (320 : ℝ) / 1600 = 16 / 80 by norm_num,
    show ((320 : ℝ) + 20) / 1600 = (16 + 1) / 80 by norm_num] using h

theorem hpThetaJensenSixthBatch017_integral_bounds :
    hpThetaJensenSixthRectangleLower 17 ≤
        (∫ u : ℝ in Set.Ioo (17 / 80 : ℝ) ((17 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (17 / 80 : ℝ) ((17 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenSixthRectangleUpper 17 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch017Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch017Lower]
  have h := hpThetaJensen_sixthBatchIntegral_of_kernelBounds (340 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch017Lower hpThetaJensenCellsBatch017Upper hL
    hpThetaJensenCellsBatch017_bounds
  simpa only [hpThetaJensenSixthRectangleLower, hpThetaJensenSixthRectangleUpper,
    add_zero, show (340 : ℝ) / 1600 = 17 / 80 by norm_num,
    show ((340 : ℝ) + 20) / 1600 = (17 + 1) / 80 by norm_num] using h

theorem hpThetaJensenSixthBatch018_integral_bounds :
    hpThetaJensenSixthRectangleLower 18 ≤
        (∫ u : ℝ in Set.Ioo (18 / 80 : ℝ) ((18 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (18 / 80 : ℝ) ((18 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenSixthRectangleUpper 18 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch018Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch018Lower]
  have h := hpThetaJensen_sixthBatchIntegral_of_kernelBounds (360 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch018Lower hpThetaJensenCellsBatch018Upper hL
    hpThetaJensenCellsBatch018_bounds
  simpa only [hpThetaJensenSixthRectangleLower, hpThetaJensenSixthRectangleUpper,
    add_zero, show (360 : ℝ) / 1600 = 18 / 80 by norm_num,
    show ((360 : ℝ) + 20) / 1600 = (18 + 1) / 80 by norm_num] using h

theorem hpThetaJensenSixthBatch019_integral_bounds :
    hpThetaJensenSixthRectangleLower 19 ≤
        (∫ u : ℝ in Set.Ioo (19 / 80 : ℝ) ((19 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (19 / 80 : ℝ) ((19 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenSixthRectangleUpper 19 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch019Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch019Lower]
  have h := hpThetaJensen_sixthBatchIntegral_of_kernelBounds (380 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch019Lower hpThetaJensenCellsBatch019Upper hL
    hpThetaJensenCellsBatch019_bounds
  simpa only [hpThetaJensenSixthRectangleLower, hpThetaJensenSixthRectangleUpper,
    add_zero, show (380 : ℝ) / 1600 = 19 / 80 by norm_num,
    show ((380 : ℝ) + 20) / 1600 = (19 + 1) / 80 by norm_num] using h

theorem hpThetaJensenSixthBatch020_integral_bounds :
    hpThetaJensenSixthRectangleLower 20 ≤
        (∫ u : ℝ in Set.Ioo (20 / 80 : ℝ) ((20 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (20 / 80 : ℝ) ((20 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenSixthRectangleUpper 20 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch020Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch020Lower]
  have h := hpThetaJensen_sixthBatchIntegral_of_kernelBounds (400 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch020Lower hpThetaJensenCellsBatch020Upper hL
    hpThetaJensenCellsBatch020_bounds
  simpa only [hpThetaJensenSixthRectangleLower, hpThetaJensenSixthRectangleUpper,
    add_zero, show (400 : ℝ) / 1600 = 20 / 80 by norm_num,
    show ((400 : ℝ) + 20) / 1600 = (20 + 1) / 80 by norm_num] using h

theorem hpThetaJensenSixthBatch021_integral_bounds :
    hpThetaJensenSixthRectangleLower 21 ≤
        (∫ u : ℝ in Set.Ioo (21 / 80 : ℝ) ((21 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (21 / 80 : ℝ) ((21 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenSixthRectangleUpper 21 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch021Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch021Lower]
  have h := hpThetaJensen_sixthBatchIntegral_of_kernelBounds (420 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch021Lower hpThetaJensenCellsBatch021Upper hL
    hpThetaJensenCellsBatch021_bounds
  simpa only [hpThetaJensenSixthRectangleLower, hpThetaJensenSixthRectangleUpper,
    add_zero, show (420 : ℝ) / 1600 = 21 / 80 by norm_num,
    show ((420 : ℝ) + 20) / 1600 = (21 + 1) / 80 by norm_num] using h

theorem hpThetaJensenSixthBatch022_integral_bounds :
    hpThetaJensenSixthRectangleLower 22 ≤
        (∫ u : ℝ in Set.Ioo (22 / 80 : ℝ) ((22 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (22 / 80 : ℝ) ((22 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenSixthRectangleUpper 22 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch022Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch022Lower]
  have h := hpThetaJensen_sixthBatchIntegral_of_kernelBounds (440 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch022Lower hpThetaJensenCellsBatch022Upper hL
    hpThetaJensenCellsBatch022_bounds
  simpa only [hpThetaJensenSixthRectangleLower, hpThetaJensenSixthRectangleUpper,
    add_zero, show (440 : ℝ) / 1600 = 22 / 80 by norm_num,
    show ((440 : ℝ) + 20) / 1600 = (22 + 1) / 80 by norm_num] using h

theorem hpThetaJensenSixthBatch023_integral_bounds :
    hpThetaJensenSixthRectangleLower 23 ≤
        (∫ u : ℝ in Set.Ioo (23 / 80 : ℝ) ((23 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (23 / 80 : ℝ) ((23 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenSixthRectangleUpper 23 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch023Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch023Lower]
  have h := hpThetaJensen_sixthBatchIntegral_of_kernelBounds (460 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch023Lower hpThetaJensenCellsBatch023Upper hL
    hpThetaJensenCellsBatch023_bounds
  simpa only [hpThetaJensenSixthRectangleLower, hpThetaJensenSixthRectangleUpper,
    add_zero, show (460 : ℝ) / 1600 = 23 / 80 by norm_num,
    show ((460 : ℝ) + 20) / 1600 = (23 + 1) / 80 by norm_num] using h

theorem hpThetaJensenSixthBatch024_integral_bounds :
    hpThetaJensenSixthRectangleLower 24 ≤
        (∫ u : ℝ in Set.Ioo (24 / 80 : ℝ) ((24 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (24 / 80 : ℝ) ((24 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenSixthRectangleUpper 24 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch024Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch024Lower]
  have h := hpThetaJensen_sixthBatchIntegral_of_kernelBounds (480 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch024Lower hpThetaJensenCellsBatch024Upper hL
    hpThetaJensenCellsBatch024_bounds
  simpa only [hpThetaJensenSixthRectangleLower, hpThetaJensenSixthRectangleUpper,
    add_zero, show (480 : ℝ) / 1600 = 24 / 80 by norm_num,
    show ((480 : ℝ) + 20) / 1600 = (24 + 1) / 80 by norm_num] using h

theorem hpThetaJensenSixthBatch025_integral_bounds :
    hpThetaJensenSixthRectangleLower 25 ≤
        (∫ u : ℝ in Set.Ioo (25 / 80 : ℝ) ((25 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (25 / 80 : ℝ) ((25 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenSixthRectangleUpper 25 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch025Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch025Lower]
  have h := hpThetaJensen_sixthBatchIntegral_of_kernelBounds (500 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch025Lower hpThetaJensenCellsBatch025Upper hL
    hpThetaJensenCellsBatch025_bounds
  simpa only [hpThetaJensenSixthRectangleLower, hpThetaJensenSixthRectangleUpper,
    add_zero, show (500 : ℝ) / 1600 = 25 / 80 by norm_num,
    show ((500 : ℝ) + 20) / 1600 = (25 + 1) / 80 by norm_num] using h

theorem hpThetaJensenSixthBatch026_integral_bounds :
    hpThetaJensenSixthRectangleLower 26 ≤
        (∫ u : ℝ in Set.Ioo (26 / 80 : ℝ) ((26 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (26 / 80 : ℝ) ((26 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenSixthRectangleUpper 26 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch026Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch026Lower]
  have h := hpThetaJensen_sixthBatchIntegral_of_kernelBounds (520 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch026Lower hpThetaJensenCellsBatch026Upper hL
    hpThetaJensenCellsBatch026_bounds
  simpa only [hpThetaJensenSixthRectangleLower, hpThetaJensenSixthRectangleUpper,
    add_zero, show (520 : ℝ) / 1600 = 26 / 80 by norm_num,
    show ((520 : ℝ) + 20) / 1600 = (26 + 1) / 80 by norm_num] using h

theorem hpThetaJensenSixthBatch027_integral_bounds :
    hpThetaJensenSixthRectangleLower 27 ≤
        (∫ u : ℝ in Set.Ioo (27 / 80 : ℝ) ((27 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (27 / 80 : ℝ) ((27 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenSixthRectangleUpper 27 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch027Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch027Lower]
  have h := hpThetaJensen_sixthBatchIntegral_of_kernelBounds (540 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch027Lower hpThetaJensenCellsBatch027Upper hL
    hpThetaJensenCellsBatch027_bounds
  simpa only [hpThetaJensenSixthRectangleLower, hpThetaJensenSixthRectangleUpper,
    add_zero, show (540 : ℝ) / 1600 = 27 / 80 by norm_num,
    show ((540 : ℝ) + 20) / 1600 = (27 + 1) / 80 by norm_num] using h

theorem hpThetaJensenSixthBatch028_integral_bounds :
    hpThetaJensenSixthRectangleLower 28 ≤
        (∫ u : ℝ in Set.Ioo (28 / 80 : ℝ) ((28 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (28 / 80 : ℝ) ((28 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenSixthRectangleUpper 28 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch028Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch028Lower]
  have h := hpThetaJensen_sixthBatchIntegral_of_kernelBounds (560 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch028Lower hpThetaJensenCellsBatch028Upper hL
    hpThetaJensenCellsBatch028_bounds
  simpa only [hpThetaJensenSixthRectangleLower, hpThetaJensenSixthRectangleUpper,
    add_zero, show (560 : ℝ) / 1600 = 28 / 80 by norm_num,
    show ((560 : ℝ) + 20) / 1600 = (28 + 1) / 80 by norm_num] using h

theorem hpThetaJensenSixthBatch029_integral_bounds :
    hpThetaJensenSixthRectangleLower 29 ≤
        (∫ u : ℝ in Set.Ioo (29 / 80 : ℝ) ((29 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (29 / 80 : ℝ) ((29 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenSixthRectangleUpper 29 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch029Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch029Lower]
  have h := hpThetaJensen_sixthBatchIntegral_of_kernelBounds (580 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch029Lower hpThetaJensenCellsBatch029Upper hL
    hpThetaJensenCellsBatch029_bounds
  simpa only [hpThetaJensenSixthRectangleLower, hpThetaJensenSixthRectangleUpper,
    add_zero, show (580 : ℝ) / 1600 = 29 / 80 by norm_num,
    show ((580 : ℝ) + 20) / 1600 = (29 + 1) / 80 by norm_num] using h

theorem hpThetaJensenSixthBatch030_integral_bounds :
    hpThetaJensenSixthRectangleLower 30 ≤
        (∫ u : ℝ in Set.Ioo (30 / 80 : ℝ) ((30 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (30 / 80 : ℝ) ((30 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenSixthRectangleUpper 30 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch030Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch030Lower]
  have h := hpThetaJensen_sixthBatchIntegral_of_kernelBounds (600 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch030Lower hpThetaJensenCellsBatch030Upper hL
    hpThetaJensenCellsBatch030_bounds
  simpa only [hpThetaJensenSixthRectangleLower, hpThetaJensenSixthRectangleUpper,
    add_zero, show (600 : ℝ) / 1600 = 30 / 80 by norm_num,
    show ((600 : ℝ) + 20) / 1600 = (30 + 1) / 80 by norm_num] using h

theorem hpThetaJensenSixthBatch031_integral_bounds :
    hpThetaJensenSixthRectangleLower 31 ≤
        (∫ u : ℝ in Set.Ioo (31 / 80 : ℝ) ((31 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (31 / 80 : ℝ) ((31 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenSixthRectangleUpper 31 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch031Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch031Lower]
  have h := hpThetaJensen_sixthBatchIntegral_of_kernelBounds (620 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch031Lower hpThetaJensenCellsBatch031Upper hL
    hpThetaJensenCellsBatch031_bounds
  simpa only [hpThetaJensenSixthRectangleLower, hpThetaJensenSixthRectangleUpper,
    add_zero, show (620 : ℝ) / 1600 = 31 / 80 by norm_num,
    show ((620 : ℝ) + 20) / 1600 = (31 + 1) / 80 by norm_num] using h

theorem hpThetaJensenSixthBatch032_integral_bounds :
    hpThetaJensenSixthRectangleLower 32 ≤
        (∫ u : ℝ in Set.Ioo (32 / 80 : ℝ) ((32 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (32 / 80 : ℝ) ((32 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenSixthRectangleUpper 32 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch032Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch032Lower]
  have h := hpThetaJensen_sixthBatchIntegral_of_kernelBounds (640 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch032Lower hpThetaJensenCellsBatch032Upper hL
    hpThetaJensenCellsBatch032_bounds
  simpa only [hpThetaJensenSixthRectangleLower, hpThetaJensenSixthRectangleUpper,
    add_zero, show (640 : ℝ) / 1600 = 32 / 80 by norm_num,
    show ((640 : ℝ) + 20) / 1600 = (32 + 1) / 80 by norm_num] using h

theorem hpThetaJensenSixthBatch033_integral_bounds :
    hpThetaJensenSixthRectangleLower 33 ≤
        (∫ u : ℝ in Set.Ioo (33 / 80 : ℝ) ((33 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (33 / 80 : ℝ) ((33 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenSixthRectangleUpper 33 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch033Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch033Lower]
  have h := hpThetaJensen_sixthBatchIntegral_of_kernelBounds (660 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch033Lower hpThetaJensenCellsBatch033Upper hL
    hpThetaJensenCellsBatch033_bounds
  simpa only [hpThetaJensenSixthRectangleLower, hpThetaJensenSixthRectangleUpper,
    add_zero, show (660 : ℝ) / 1600 = 33 / 80 by norm_num,
    show ((660 : ℝ) + 20) / 1600 = (33 + 1) / 80 by norm_num] using h

theorem hpThetaJensenSixthBatch034_integral_bounds :
    hpThetaJensenSixthRectangleLower 34 ≤
        (∫ u : ℝ in Set.Ioo (34 / 80 : ℝ) ((34 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (34 / 80 : ℝ) ((34 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenSixthRectangleUpper 34 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch034Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch034Lower]
  have h := hpThetaJensen_sixthBatchIntegral_of_kernelBounds (680 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch034Lower hpThetaJensenCellsBatch034Upper hL
    hpThetaJensenCellsBatch034_bounds
  simpa only [hpThetaJensenSixthRectangleLower, hpThetaJensenSixthRectangleUpper,
    add_zero, show (680 : ℝ) / 1600 = 34 / 80 by norm_num,
    show ((680 : ℝ) + 20) / 1600 = (34 + 1) / 80 by norm_num] using h

theorem hpThetaJensenSixthBatch035_integral_bounds :
    hpThetaJensenSixthRectangleLower 35 ≤
        (∫ u : ℝ in Set.Ioo (35 / 80 : ℝ) ((35 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (35 / 80 : ℝ) ((35 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenSixthRectangleUpper 35 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch035Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch035Lower]
  have h := hpThetaJensen_sixthBatchIntegral_of_kernelBounds (700 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch035Lower hpThetaJensenCellsBatch035Upper hL
    hpThetaJensenCellsBatch035_bounds
  simpa only [hpThetaJensenSixthRectangleLower, hpThetaJensenSixthRectangleUpper,
    add_zero, show (700 : ℝ) / 1600 = 35 / 80 by norm_num,
    show ((700 : ℝ) + 20) / 1600 = (35 + 1) / 80 by norm_num] using h

theorem hpThetaJensenSixthBatch036_integral_bounds :
    hpThetaJensenSixthRectangleLower 36 ≤
        (∫ u : ℝ in Set.Ioo (36 / 80 : ℝ) ((36 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (36 / 80 : ℝ) ((36 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenSixthRectangleUpper 36 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch036Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch036Lower]
  have h := hpThetaJensen_sixthBatchIntegral_of_kernelBounds (720 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch036Lower hpThetaJensenCellsBatch036Upper hL
    hpThetaJensenCellsBatch036_bounds
  simpa only [hpThetaJensenSixthRectangleLower, hpThetaJensenSixthRectangleUpper,
    add_zero, show (720 : ℝ) / 1600 = 36 / 80 by norm_num,
    show ((720 : ℝ) + 20) / 1600 = (36 + 1) / 80 by norm_num] using h

theorem hpThetaJensenSixthBatch037_integral_bounds :
    hpThetaJensenSixthRectangleLower 37 ≤
        (∫ u : ℝ in Set.Ioo (37 / 80 : ℝ) ((37 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (37 / 80 : ℝ) ((37 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenSixthRectangleUpper 37 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch037Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch037Lower]
  have h := hpThetaJensen_sixthBatchIntegral_of_kernelBounds (740 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch037Lower hpThetaJensenCellsBatch037Upper hL
    hpThetaJensenCellsBatch037_bounds
  simpa only [hpThetaJensenSixthRectangleLower, hpThetaJensenSixthRectangleUpper,
    add_zero, show (740 : ℝ) / 1600 = 37 / 80 by norm_num,
    show ((740 : ℝ) + 20) / 1600 = (37 + 1) / 80 by norm_num] using h

theorem hpThetaJensenSixthBatch038_integral_bounds :
    hpThetaJensenSixthRectangleLower 38 ≤
        (∫ u : ℝ in Set.Ioo (38 / 80 : ℝ) ((38 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (38 / 80 : ℝ) ((38 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenSixthRectangleUpper 38 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch038Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch038Lower]
  have h := hpThetaJensen_sixthBatchIntegral_of_kernelBounds (760 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch038Lower hpThetaJensenCellsBatch038Upper hL
    hpThetaJensenCellsBatch038_bounds
  simpa only [hpThetaJensenSixthRectangleLower, hpThetaJensenSixthRectangleUpper,
    add_zero, show (760 : ℝ) / 1600 = 38 / 80 by norm_num,
    show ((760 : ℝ) + 20) / 1600 = (38 + 1) / 80 by norm_num] using h

theorem hpThetaJensenSixthBatch039_integral_bounds :
    hpThetaJensenSixthRectangleLower 39 ≤
        (∫ u : ℝ in Set.Ioo (39 / 80 : ℝ) ((39 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (39 / 80 : ℝ) ((39 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenSixthRectangleUpper 39 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch039Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch039Lower]
  have h := hpThetaJensen_sixthBatchIntegral_of_kernelBounds (780 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch039Lower hpThetaJensenCellsBatch039Upper hL
    hpThetaJensenCellsBatch039_bounds
  simpa only [hpThetaJensenSixthRectangleLower, hpThetaJensenSixthRectangleUpper,
    add_zero, show (780 : ℝ) / 1600 = 39 / 80 by norm_num,
    show ((780 : ℝ) + 20) / 1600 = (39 + 1) / 80 by norm_num] using h

theorem hpThetaJensenSixthBatch040_integral_bounds :
    hpThetaJensenSixthRectangleLower 40 ≤
        (∫ u : ℝ in Set.Ioo (40 / 80 : ℝ) ((40 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (40 / 80 : ℝ) ((40 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenSixthRectangleUpper 40 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch040Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch040Lower]
  have h := hpThetaJensen_sixthBatchIntegral_of_kernelBounds (800 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch040Lower hpThetaJensenCellsBatch040Upper hL
    hpThetaJensenCellsBatch040_bounds
  simpa only [hpThetaJensenSixthRectangleLower, hpThetaJensenSixthRectangleUpper,
    add_zero, show (800 : ℝ) / 1600 = 40 / 80 by norm_num,
    show ((800 : ℝ) + 20) / 1600 = (40 + 1) / 80 by norm_num] using h

theorem hpThetaJensenSixthBatch041_integral_bounds :
    hpThetaJensenSixthRectangleLower 41 ≤
        (∫ u : ℝ in Set.Ioo (41 / 80 : ℝ) ((41 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (41 / 80 : ℝ) ((41 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenSixthRectangleUpper 41 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch041Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch041Lower]
  have h := hpThetaJensen_sixthBatchIntegral_of_kernelBounds (820 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch041Lower hpThetaJensenCellsBatch041Upper hL
    hpThetaJensenCellsBatch041_bounds
  simpa only [hpThetaJensenSixthRectangleLower, hpThetaJensenSixthRectangleUpper,
    add_zero, show (820 : ℝ) / 1600 = 41 / 80 by norm_num,
    show ((820 : ℝ) + 20) / 1600 = (41 + 1) / 80 by norm_num] using h

theorem hpThetaJensenSixthBatch042_integral_bounds :
    hpThetaJensenSixthRectangleLower 42 ≤
        (∫ u : ℝ in Set.Ioo (42 / 80 : ℝ) ((42 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (42 / 80 : ℝ) ((42 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenSixthRectangleUpper 42 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch042Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch042Lower]
  have h := hpThetaJensen_sixthBatchIntegral_of_kernelBounds (840 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch042Lower hpThetaJensenCellsBatch042Upper hL
    hpThetaJensenCellsBatch042_bounds
  simpa only [hpThetaJensenSixthRectangleLower, hpThetaJensenSixthRectangleUpper,
    add_zero, show (840 : ℝ) / 1600 = 42 / 80 by norm_num,
    show ((840 : ℝ) + 20) / 1600 = (42 + 1) / 80 by norm_num] using h

theorem hpThetaJensenSixthBatch043_integral_bounds :
    hpThetaJensenSixthRectangleLower 43 ≤
        (∫ u : ℝ in Set.Ioo (43 / 80 : ℝ) ((43 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (43 / 80 : ℝ) ((43 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenSixthRectangleUpper 43 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch043Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch043Lower]
  have h := hpThetaJensen_sixthBatchIntegral_of_kernelBounds (860 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch043Lower hpThetaJensenCellsBatch043Upper hL
    hpThetaJensenCellsBatch043_bounds
  simpa only [hpThetaJensenSixthRectangleLower, hpThetaJensenSixthRectangleUpper,
    add_zero, show (860 : ℝ) / 1600 = 43 / 80 by norm_num,
    show ((860 : ℝ) + 20) / 1600 = (43 + 1) / 80 by norm_num] using h

theorem hpThetaJensenSixthBatch044_integral_bounds :
    hpThetaJensenSixthRectangleLower 44 ≤
        (∫ u : ℝ in Set.Ioo (44 / 80 : ℝ) ((44 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (44 / 80 : ℝ) ((44 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenSixthRectangleUpper 44 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch044Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch044Lower]
  have h := hpThetaJensen_sixthBatchIntegral_of_kernelBounds (880 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch044Lower hpThetaJensenCellsBatch044Upper hL
    hpThetaJensenCellsBatch044_bounds
  simpa only [hpThetaJensenSixthRectangleLower, hpThetaJensenSixthRectangleUpper,
    add_zero, show (880 : ℝ) / 1600 = 44 / 80 by norm_num,
    show ((880 : ℝ) + 20) / 1600 = (44 + 1) / 80 by norm_num] using h

theorem hpThetaJensenSixthBatch045_integral_bounds :
    hpThetaJensenSixthRectangleLower 45 ≤
        (∫ u : ℝ in Set.Ioo (45 / 80 : ℝ) ((45 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (45 / 80 : ℝ) ((45 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenSixthRectangleUpper 45 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch045Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch045Lower]
  have h := hpThetaJensen_sixthBatchIntegral_of_kernelBounds (900 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch045Lower hpThetaJensenCellsBatch045Upper hL
    hpThetaJensenCellsBatch045_bounds
  simpa only [hpThetaJensenSixthRectangleLower, hpThetaJensenSixthRectangleUpper,
    add_zero, show (900 : ℝ) / 1600 = 45 / 80 by norm_num,
    show ((900 : ℝ) + 20) / 1600 = (45 + 1) / 80 by norm_num] using h

theorem hpThetaJensenSixthBatch046_integral_bounds :
    hpThetaJensenSixthRectangleLower 46 ≤
        (∫ u : ℝ in Set.Ioo (46 / 80 : ℝ) ((46 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (46 / 80 : ℝ) ((46 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenSixthRectangleUpper 46 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch046Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch046Lower]
  have h := hpThetaJensen_sixthBatchIntegral_of_kernelBounds (920 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch046Lower hpThetaJensenCellsBatch046Upper hL
    hpThetaJensenCellsBatch046_bounds
  simpa only [hpThetaJensenSixthRectangleLower, hpThetaJensenSixthRectangleUpper,
    add_zero, show (920 : ℝ) / 1600 = 46 / 80 by norm_num,
    show ((920 : ℝ) + 20) / 1600 = (46 + 1) / 80 by norm_num] using h

theorem hpThetaJensenSixthBatch047_integral_bounds :
    hpThetaJensenSixthRectangleLower 47 ≤
        (∫ u : ℝ in Set.Ioo (47 / 80 : ℝ) ((47 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (47 / 80 : ℝ) ((47 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenSixthRectangleUpper 47 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch047Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch047Lower]
  have h := hpThetaJensen_sixthBatchIntegral_of_kernelBounds (940 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch047Lower hpThetaJensenCellsBatch047Upper hL
    hpThetaJensenCellsBatch047_bounds
  simpa only [hpThetaJensenSixthRectangleLower, hpThetaJensenSixthRectangleUpper,
    add_zero, show (940 : ℝ) / 1600 = 47 / 80 by norm_num,
    show ((940 : ℝ) + 20) / 1600 = (47 + 1) / 80 by norm_num] using h

theorem hpThetaJensenSixthBatch048_integral_bounds :
    hpThetaJensenSixthRectangleLower 48 ≤
        (∫ u : ℝ in Set.Ioo (48 / 80 : ℝ) ((48 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (48 / 80 : ℝ) ((48 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenSixthRectangleUpper 48 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch048Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch048Lower]
  have h := hpThetaJensen_sixthBatchIntegral_of_kernelBounds (960 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch048Lower hpThetaJensenCellsBatch048Upper hL
    hpThetaJensenCellsBatch048_bounds
  simpa only [hpThetaJensenSixthRectangleLower, hpThetaJensenSixthRectangleUpper,
    add_zero, show (960 : ℝ) / 1600 = 48 / 80 by norm_num,
    show ((960 : ℝ) + 20) / 1600 = (48 + 1) / 80 by norm_num] using h

theorem hpThetaJensenSixthBatch049_integral_bounds :
    hpThetaJensenSixthRectangleLower 49 ≤
        (∫ u : ℝ in Set.Ioo (49 / 80 : ℝ) ((49 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (49 / 80 : ℝ) ((49 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenSixthRectangleUpper 49 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch049Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch049Lower]
  have h := hpThetaJensen_sixthBatchIntegral_of_kernelBounds (980 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch049Lower hpThetaJensenCellsBatch049Upper hL
    hpThetaJensenCellsBatch049_bounds
  simpa only [hpThetaJensenSixthRectangleLower, hpThetaJensenSixthRectangleUpper,
    add_zero, show (980 : ℝ) / 1600 = 49 / 80 by norm_num,
    show ((980 : ℝ) + 20) / 1600 = (49 + 1) / 80 by norm_num] using h

theorem hpThetaJensenSixthBatch050_integral_bounds :
    hpThetaJensenSixthRectangleLower 50 ≤
        (∫ u : ℝ in Set.Ioo (50 / 80 : ℝ) ((50 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (50 / 80 : ℝ) ((50 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenSixthRectangleUpper 50 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch050Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch050Lower]
  have h := hpThetaJensen_sixthBatchIntegral_of_kernelBounds (1000 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch050Lower hpThetaJensenCellsBatch050Upper hL
    hpThetaJensenCellsBatch050_bounds
  simpa only [hpThetaJensenSixthRectangleLower, hpThetaJensenSixthRectangleUpper,
    add_zero, show (1000 : ℝ) / 1600 = 50 / 80 by norm_num,
    show ((1000 : ℝ) + 20) / 1600 = (50 + 1) / 80 by norm_num] using h

theorem hpThetaJensenSixthBatch051_integral_bounds :
    hpThetaJensenSixthRectangleLower 51 ≤
        (∫ u : ℝ in Set.Ioo (51 / 80 : ℝ) ((51 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (51 / 80 : ℝ) ((51 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenSixthRectangleUpper 51 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch051Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch051Lower]
  have h := hpThetaJensen_sixthBatchIntegral_of_kernelBounds (1020 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch051Lower hpThetaJensenCellsBatch051Upper hL
    hpThetaJensenCellsBatch051_bounds
  simpa only [hpThetaJensenSixthRectangleLower, hpThetaJensenSixthRectangleUpper,
    add_zero, show (1020 : ℝ) / 1600 = 51 / 80 by norm_num,
    show ((1020 : ℝ) + 20) / 1600 = (51 + 1) / 80 by norm_num] using h

theorem hpThetaJensenSixthBatch052_integral_bounds :
    hpThetaJensenSixthRectangleLower 52 ≤
        (∫ u : ℝ in Set.Ioo (52 / 80 : ℝ) ((52 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (52 / 80 : ℝ) ((52 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenSixthRectangleUpper 52 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch052Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch052Lower]
  have h := hpThetaJensen_sixthBatchIntegral_of_kernelBounds (1040 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch052Lower hpThetaJensenCellsBatch052Upper hL
    hpThetaJensenCellsBatch052_bounds
  simpa only [hpThetaJensenSixthRectangleLower, hpThetaJensenSixthRectangleUpper,
    add_zero, show (1040 : ℝ) / 1600 = 52 / 80 by norm_num,
    show ((1040 : ℝ) + 20) / 1600 = (52 + 1) / 80 by norm_num] using h

theorem hpThetaJensenSixthBatch053_integral_bounds :
    hpThetaJensenSixthRectangleLower 53 ≤
        (∫ u : ℝ in Set.Ioo (53 / 80 : ℝ) ((53 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (53 / 80 : ℝ) ((53 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenSixthRectangleUpper 53 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch053Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch053Lower]
  have h := hpThetaJensen_sixthBatchIntegral_of_kernelBounds (1060 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch053Lower hpThetaJensenCellsBatch053Upper hL
    hpThetaJensenCellsBatch053_bounds
  simpa only [hpThetaJensenSixthRectangleLower, hpThetaJensenSixthRectangleUpper,
    add_zero, show (1060 : ℝ) / 1600 = 53 / 80 by norm_num,
    show ((1060 : ℝ) + 20) / 1600 = (53 + 1) / 80 by norm_num] using h

theorem hpThetaJensenSixthBatch054_integral_bounds :
    hpThetaJensenSixthRectangleLower 54 ≤
        (∫ u : ℝ in Set.Ioo (54 / 80 : ℝ) ((54 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (54 / 80 : ℝ) ((54 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenSixthRectangleUpper 54 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch054Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch054Lower]
  have h := hpThetaJensen_sixthBatchIntegral_of_kernelBounds (1080 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch054Lower hpThetaJensenCellsBatch054Upper hL
    hpThetaJensenCellsBatch054_bounds
  simpa only [hpThetaJensenSixthRectangleLower, hpThetaJensenSixthRectangleUpper,
    add_zero, show (1080 : ℝ) / 1600 = 54 / 80 by norm_num,
    show ((1080 : ℝ) + 20) / 1600 = (54 + 1) / 80 by norm_num] using h

theorem hpThetaJensenSixthBatch055_integral_bounds :
    hpThetaJensenSixthRectangleLower 55 ≤
        (∫ u : ℝ in Set.Ioo (55 / 80 : ℝ) ((55 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (55 / 80 : ℝ) ((55 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenSixthRectangleUpper 55 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch055Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch055Lower]
  have h := hpThetaJensen_sixthBatchIntegral_of_kernelBounds (1100 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch055Lower hpThetaJensenCellsBatch055Upper hL
    hpThetaJensenCellsBatch055_bounds
  simpa only [hpThetaJensenSixthRectangleLower, hpThetaJensenSixthRectangleUpper,
    add_zero, show (1100 : ℝ) / 1600 = 55 / 80 by norm_num,
    show ((1100 : ℝ) + 20) / 1600 = (55 + 1) / 80 by norm_num] using h

theorem hpThetaJensenSixthBatch056_integral_bounds :
    hpThetaJensenSixthRectangleLower 56 ≤
        (∫ u : ℝ in Set.Ioo (56 / 80 : ℝ) ((56 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (56 / 80 : ℝ) ((56 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenSixthRectangleUpper 56 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch056Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch056Lower]
  have h := hpThetaJensen_sixthBatchIntegral_of_kernelBounds (1120 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch056Lower hpThetaJensenCellsBatch056Upper hL
    hpThetaJensenCellsBatch056_bounds
  simpa only [hpThetaJensenSixthRectangleLower, hpThetaJensenSixthRectangleUpper,
    add_zero, show (1120 : ℝ) / 1600 = 56 / 80 by norm_num,
    show ((1120 : ℝ) + 20) / 1600 = (56 + 1) / 80 by norm_num] using h

theorem hpThetaJensenSixthBatch057_integral_bounds :
    hpThetaJensenSixthRectangleLower 57 ≤
        (∫ u : ℝ in Set.Ioo (57 / 80 : ℝ) ((57 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (57 / 80 : ℝ) ((57 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenSixthRectangleUpper 57 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch057Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch057Lower]
  have h := hpThetaJensen_sixthBatchIntegral_of_kernelBounds (1140 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch057Lower hpThetaJensenCellsBatch057Upper hL
    hpThetaJensenCellsBatch057_bounds
  simpa only [hpThetaJensenSixthRectangleLower, hpThetaJensenSixthRectangleUpper,
    add_zero, show (1140 : ℝ) / 1600 = 57 / 80 by norm_num,
    show ((1140 : ℝ) + 20) / 1600 = (57 + 1) / 80 by norm_num] using h

theorem hpThetaJensenSixthBatch058_integral_bounds :
    hpThetaJensenSixthRectangleLower 58 ≤
        (∫ u : ℝ in Set.Ioo (58 / 80 : ℝ) ((58 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (58 / 80 : ℝ) ((58 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenSixthRectangleUpper 58 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch058Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch058Lower]
  have h := hpThetaJensen_sixthBatchIntegral_of_kernelBounds (1160 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch058Lower hpThetaJensenCellsBatch058Upper hL
    hpThetaJensenCellsBatch058_bounds
  simpa only [hpThetaJensenSixthRectangleLower, hpThetaJensenSixthRectangleUpper,
    add_zero, show (1160 : ℝ) / 1600 = 58 / 80 by norm_num,
    show ((1160 : ℝ) + 20) / 1600 = (58 + 1) / 80 by norm_num] using h

theorem hpThetaJensenSixthBatch059_integral_bounds :
    hpThetaJensenSixthRectangleLower 59 ≤
        (∫ u : ℝ in Set.Ioo (59 / 80 : ℝ) ((59 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (59 / 80 : ℝ) ((59 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenSixthRectangleUpper 59 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch059Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch059Lower]
  have h := hpThetaJensen_sixthBatchIntegral_of_kernelBounds (1180 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch059Lower hpThetaJensenCellsBatch059Upper hL
    hpThetaJensenCellsBatch059_bounds
  simpa only [hpThetaJensenSixthRectangleLower, hpThetaJensenSixthRectangleUpper,
    add_zero, show (1180 : ℝ) / 1600 = 59 / 80 by norm_num,
    show ((1180 : ℝ) + 20) / 1600 = (59 + 1) / 80 by norm_num] using h

theorem hpThetaJensenSixthBatch060_integral_bounds :
    hpThetaJensenSixthRectangleLower 60 ≤
        (∫ u : ℝ in Set.Ioo (60 / 80 : ℝ) ((60 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (60 / 80 : ℝ) ((60 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenSixthRectangleUpper 60 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch060Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch060Lower]
  have h := hpThetaJensen_sixthBatchIntegral_of_kernelBounds (1200 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch060Lower hpThetaJensenCellsBatch060Upper hL
    hpThetaJensenCellsBatch060_bounds
  simpa only [hpThetaJensenSixthRectangleLower, hpThetaJensenSixthRectangleUpper,
    add_zero, show (1200 : ℝ) / 1600 = 60 / 80 by norm_num,
    show ((1200 : ℝ) + 20) / 1600 = (60 + 1) / 80 by norm_num] using h

theorem hpThetaJensenSixthBatch061_integral_bounds :
    hpThetaJensenSixthRectangleLower 61 ≤
        (∫ u : ℝ in Set.Ioo (61 / 80 : ℝ) ((61 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (61 / 80 : ℝ) ((61 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenSixthRectangleUpper 61 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch061Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch061Lower]
  have h := hpThetaJensen_sixthBatchIntegral_of_kernelBounds (1220 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch061Lower hpThetaJensenCellsBatch061Upper hL
    hpThetaJensenCellsBatch061_bounds
  simpa only [hpThetaJensenSixthRectangleLower, hpThetaJensenSixthRectangleUpper,
    add_zero, show (1220 : ℝ) / 1600 = 61 / 80 by norm_num,
    show ((1220 : ℝ) + 20) / 1600 = (61 + 1) / 80 by norm_num] using h

theorem hpThetaJensenSixthBatch062_integral_bounds :
    hpThetaJensenSixthRectangleLower 62 ≤
        (∫ u : ℝ in Set.Ioo (62 / 80 : ℝ) ((62 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (62 / 80 : ℝ) ((62 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenSixthRectangleUpper 62 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch062Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch062Lower]
  have h := hpThetaJensen_sixthBatchIntegral_of_kernelBounds (1240 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch062Lower hpThetaJensenCellsBatch062Upper hL
    hpThetaJensenCellsBatch062_bounds
  simpa only [hpThetaJensenSixthRectangleLower, hpThetaJensenSixthRectangleUpper,
    add_zero, show (1240 : ℝ) / 1600 = 62 / 80 by norm_num,
    show ((1240 : ℝ) + 20) / 1600 = (62 + 1) / 80 by norm_num] using h

theorem hpThetaJensenSixthBatch063_integral_bounds :
    hpThetaJensenSixthRectangleLower 63 ≤
        (∫ u : ℝ in Set.Ioo (63 / 80 : ℝ) ((63 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (63 / 80 : ℝ) ((63 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenSixthRectangleUpper 63 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch063Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch063Lower]
  have h := hpThetaJensen_sixthBatchIntegral_of_kernelBounds (1260 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch063Lower hpThetaJensenCellsBatch063Upper hL
    hpThetaJensenCellsBatch063_bounds
  simpa only [hpThetaJensenSixthRectangleLower, hpThetaJensenSixthRectangleUpper,
    add_zero, show (1260 : ℝ) / 1600 = 63 / 80 by norm_num,
    show ((1260 : ℝ) + 20) / 1600 = (63 + 1) / 80 by norm_num] using h

theorem hpThetaJensenSixthBatch064_integral_bounds :
    hpThetaJensenSixthRectangleLower 64 ≤
        (∫ u : ℝ in Set.Ioo (64 / 80 : ℝ) ((64 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (64 / 80 : ℝ) ((64 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenSixthRectangleUpper 64 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch064Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch064Lower]
  have h := hpThetaJensen_sixthBatchIntegral_of_kernelBounds (1280 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch064Lower hpThetaJensenCellsBatch064Upper hL
    hpThetaJensenCellsBatch064_bounds
  simpa only [hpThetaJensenSixthRectangleLower, hpThetaJensenSixthRectangleUpper,
    add_zero, show (1280 : ℝ) / 1600 = 64 / 80 by norm_num,
    show ((1280 : ℝ) + 20) / 1600 = (64 + 1) / 80 by norm_num] using h

theorem hpThetaJensenSixthBatch065_integral_bounds :
    hpThetaJensenSixthRectangleLower 65 ≤
        (∫ u : ℝ in Set.Ioo (65 / 80 : ℝ) ((65 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (65 / 80 : ℝ) ((65 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenSixthRectangleUpper 65 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch065Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch065Lower]
  have h := hpThetaJensen_sixthBatchIntegral_of_kernelBounds (1300 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch065Lower hpThetaJensenCellsBatch065Upper hL
    hpThetaJensenCellsBatch065_bounds
  simpa only [hpThetaJensenSixthRectangleLower, hpThetaJensenSixthRectangleUpper,
    add_zero, show (1300 : ℝ) / 1600 = 65 / 80 by norm_num,
    show ((1300 : ℝ) + 20) / 1600 = (65 + 1) / 80 by norm_num] using h

theorem hpThetaJensenSixthBatch066_integral_bounds :
    hpThetaJensenSixthRectangleLower 66 ≤
        (∫ u : ℝ in Set.Ioo (66 / 80 : ℝ) ((66 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (66 / 80 : ℝ) ((66 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenSixthRectangleUpper 66 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch066Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch066Lower]
  have h := hpThetaJensen_sixthBatchIntegral_of_kernelBounds (1320 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch066Lower hpThetaJensenCellsBatch066Upper hL
    hpThetaJensenCellsBatch066_bounds
  simpa only [hpThetaJensenSixthRectangleLower, hpThetaJensenSixthRectangleUpper,
    add_zero, show (1320 : ℝ) / 1600 = 66 / 80 by norm_num,
    show ((1320 : ℝ) + 20) / 1600 = (66 + 1) / 80 by norm_num] using h

theorem hpThetaJensenSixthBatch067_integral_bounds :
    hpThetaJensenSixthRectangleLower 67 ≤
        (∫ u : ℝ in Set.Ioo (67 / 80 : ℝ) ((67 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (67 / 80 : ℝ) ((67 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenSixthRectangleUpper 67 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch067Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch067Lower]
  have h := hpThetaJensen_sixthBatchIntegral_of_kernelBounds (1340 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch067Lower hpThetaJensenCellsBatch067Upper hL
    hpThetaJensenCellsBatch067_bounds
  simpa only [hpThetaJensenSixthRectangleLower, hpThetaJensenSixthRectangleUpper,
    add_zero, show (1340 : ℝ) / 1600 = 67 / 80 by norm_num,
    show ((1340 : ℝ) + 20) / 1600 = (67 + 1) / 80 by norm_num] using h

theorem hpThetaJensenSixthBatch068_integral_bounds :
    hpThetaJensenSixthRectangleLower 68 ≤
        (∫ u : ℝ in Set.Ioo (68 / 80 : ℝ) ((68 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (68 / 80 : ℝ) ((68 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenSixthRectangleUpper 68 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch068Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch068Lower]
  have h := hpThetaJensen_sixthBatchIntegral_of_kernelBounds (1360 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch068Lower hpThetaJensenCellsBatch068Upper hL
    hpThetaJensenCellsBatch068_bounds
  simpa only [hpThetaJensenSixthRectangleLower, hpThetaJensenSixthRectangleUpper,
    add_zero, show (1360 : ℝ) / 1600 = 68 / 80 by norm_num,
    show ((1360 : ℝ) + 20) / 1600 = (68 + 1) / 80 by norm_num] using h

theorem hpThetaJensenSixthBatch069_integral_bounds :
    hpThetaJensenSixthRectangleLower 69 ≤
        (∫ u : ℝ in Set.Ioo (69 / 80 : ℝ) ((69 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (69 / 80 : ℝ) ((69 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenSixthRectangleUpper 69 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch069Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch069Lower]
  have h := hpThetaJensen_sixthBatchIntegral_of_kernelBounds (1380 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch069Lower hpThetaJensenCellsBatch069Upper hL
    hpThetaJensenCellsBatch069_bounds
  simpa only [hpThetaJensenSixthRectangleLower, hpThetaJensenSixthRectangleUpper,
    add_zero, show (1380 : ℝ) / 1600 = 69 / 80 by norm_num,
    show ((1380 : ℝ) + 20) / 1600 = (69 + 1) / 80 by norm_num] using h

theorem hpThetaJensenSixthBatch070_integral_bounds :
    hpThetaJensenSixthRectangleLower 70 ≤
        (∫ u : ℝ in Set.Ioo (70 / 80 : ℝ) ((70 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (70 / 80 : ℝ) ((70 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenSixthRectangleUpper 70 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch070Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch070Lower]
  have h := hpThetaJensen_sixthBatchIntegral_of_kernelBounds (1400 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch070Lower hpThetaJensenCellsBatch070Upper hL
    hpThetaJensenCellsBatch070_bounds
  simpa only [hpThetaJensenSixthRectangleLower, hpThetaJensenSixthRectangleUpper,
    add_zero, show (1400 : ℝ) / 1600 = 70 / 80 by norm_num,
    show ((1400 : ℝ) + 20) / 1600 = (70 + 1) / 80 by norm_num] using h

theorem hpThetaJensenSixthBatch071_integral_bounds :
    hpThetaJensenSixthRectangleLower 71 ≤
        (∫ u : ℝ in Set.Ioo (71 / 80 : ℝ) ((71 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (71 / 80 : ℝ) ((71 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenSixthRectangleUpper 71 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch071Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch071Lower]
  have h := hpThetaJensen_sixthBatchIntegral_of_kernelBounds (1420 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch071Lower hpThetaJensenCellsBatch071Upper hL
    hpThetaJensenCellsBatch071_bounds
  simpa only [hpThetaJensenSixthRectangleLower, hpThetaJensenSixthRectangleUpper,
    add_zero, show (1420 : ℝ) / 1600 = 71 / 80 by norm_num,
    show ((1420 : ℝ) + 20) / 1600 = (71 + 1) / 80 by norm_num] using h

theorem hpThetaJensenSixthBatch072_integral_bounds :
    hpThetaJensenSixthRectangleLower 72 ≤
        (∫ u : ℝ in Set.Ioo (72 / 80 : ℝ) ((72 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (72 / 80 : ℝ) ((72 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenSixthRectangleUpper 72 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch072Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch072Lower]
  have h := hpThetaJensen_sixthBatchIntegral_of_kernelBounds (1440 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch072Lower hpThetaJensenCellsBatch072Upper hL
    hpThetaJensenCellsBatch072_bounds
  simpa only [hpThetaJensenSixthRectangleLower, hpThetaJensenSixthRectangleUpper,
    add_zero, show (1440 : ℝ) / 1600 = 72 / 80 by norm_num,
    show ((1440 : ℝ) + 20) / 1600 = (72 + 1) / 80 by norm_num] using h

theorem hpThetaJensenSixthBatch073_integral_bounds :
    hpThetaJensenSixthRectangleLower 73 ≤
        (∫ u : ℝ in Set.Ioo (73 / 80 : ℝ) ((73 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (73 / 80 : ℝ) ((73 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenSixthRectangleUpper 73 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch073Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch073Lower]
  have h := hpThetaJensen_sixthBatchIntegral_of_kernelBounds (1460 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch073Lower hpThetaJensenCellsBatch073Upper hL
    hpThetaJensenCellsBatch073_bounds
  simpa only [hpThetaJensenSixthRectangleLower, hpThetaJensenSixthRectangleUpper,
    add_zero, show (1460 : ℝ) / 1600 = 73 / 80 by norm_num,
    show ((1460 : ℝ) + 20) / 1600 = (73 + 1) / 80 by norm_num] using h

theorem hpThetaJensenSixthBatch074_integral_bounds :
    hpThetaJensenSixthRectangleLower 74 ≤
        (∫ u : ℝ in Set.Ioo (74 / 80 : ℝ) ((74 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (74 / 80 : ℝ) ((74 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenSixthRectangleUpper 74 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch074Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch074Lower]
  have h := hpThetaJensen_sixthBatchIntegral_of_kernelBounds (1480 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch074Lower hpThetaJensenCellsBatch074Upper hL
    hpThetaJensenCellsBatch074_bounds
  simpa only [hpThetaJensenSixthRectangleLower, hpThetaJensenSixthRectangleUpper,
    add_zero, show (1480 : ℝ) / 1600 = 74 / 80 by norm_num,
    show ((1480 : ℝ) + 20) / 1600 = (74 + 1) / 80 by norm_num] using h

theorem hpThetaJensenSixthBatch075_integral_bounds :
    hpThetaJensenSixthRectangleLower 75 ≤
        (∫ u : ℝ in Set.Ioo (75 / 80 : ℝ) ((75 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (75 / 80 : ℝ) ((75 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenSixthRectangleUpper 75 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch075Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch075Lower]
  have h := hpThetaJensen_sixthBatchIntegral_of_kernelBounds (1500 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch075Lower hpThetaJensenCellsBatch075Upper hL
    hpThetaJensenCellsBatch075_bounds
  simpa only [hpThetaJensenSixthRectangleLower, hpThetaJensenSixthRectangleUpper,
    add_zero, show (1500 : ℝ) / 1600 = 75 / 80 by norm_num,
    show ((1500 : ℝ) + 20) / 1600 = (75 + 1) / 80 by norm_num] using h

theorem hpThetaJensenSixthBatch076_integral_bounds :
    hpThetaJensenSixthRectangleLower 76 ≤
        (∫ u : ℝ in Set.Ioo (76 / 80 : ℝ) ((76 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (76 / 80 : ℝ) ((76 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenSixthRectangleUpper 76 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch076Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch076Lower]
  have h := hpThetaJensen_sixthBatchIntegral_of_kernelBounds (1520 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch076Lower hpThetaJensenCellsBatch076Upper hL
    hpThetaJensenCellsBatch076_bounds
  simpa only [hpThetaJensenSixthRectangleLower, hpThetaJensenSixthRectangleUpper,
    add_zero, show (1520 : ℝ) / 1600 = 76 / 80 by norm_num,
    show ((1520 : ℝ) + 20) / 1600 = (76 + 1) / 80 by norm_num] using h

theorem hpThetaJensenSixthBatch077_integral_bounds :
    hpThetaJensenSixthRectangleLower 77 ≤
        (∫ u : ℝ in Set.Ioo (77 / 80 : ℝ) ((77 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (77 / 80 : ℝ) ((77 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenSixthRectangleUpper 77 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch077Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch077Lower]
  have h := hpThetaJensen_sixthBatchIntegral_of_kernelBounds (1540 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch077Lower hpThetaJensenCellsBatch077Upper hL
    hpThetaJensenCellsBatch077_bounds
  simpa only [hpThetaJensenSixthRectangleLower, hpThetaJensenSixthRectangleUpper,
    add_zero, show (1540 : ℝ) / 1600 = 77 / 80 by norm_num,
    show ((1540 : ℝ) + 20) / 1600 = (77 + 1) / 80 by norm_num] using h

theorem hpThetaJensenSixthBatch078_integral_bounds :
    hpThetaJensenSixthRectangleLower 78 ≤
        (∫ u : ℝ in Set.Ioo (78 / 80 : ℝ) ((78 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (78 / 80 : ℝ) ((78 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenSixthRectangleUpper 78 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch078Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch078Lower]
  have h := hpThetaJensen_sixthBatchIntegral_of_kernelBounds (1560 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch078Lower hpThetaJensenCellsBatch078Upper hL
    hpThetaJensenCellsBatch078_bounds
  simpa only [hpThetaJensenSixthRectangleLower, hpThetaJensenSixthRectangleUpper,
    add_zero, show (1560 : ℝ) / 1600 = 78 / 80 by norm_num,
    show ((1560 : ℝ) + 20) / 1600 = (78 + 1) / 80 by norm_num] using h

theorem hpThetaJensenSixthBatch079_integral_bounds :
    hpThetaJensenSixthRectangleLower 79 ≤
        (∫ u : ℝ in Set.Ioo (79 / 80 : ℝ) ((79 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (79 / 80 : ℝ) ((79 + 1) / 80 : ℝ),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenSixthRectangleUpper 79 := by
  have hL (j : Fin 20) : 0 ≤ hpThetaJensenCellsBatch079Lower j.val := by
    fin_cases j <;> norm_num [hpThetaJensenCellsBatch079Lower]
  have h := hpThetaJensen_sixthBatchIntegral_of_kernelBounds (1580 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch079Lower hpThetaJensenCellsBatch079Upper hL
    hpThetaJensenCellsBatch079_bounds
  simpa only [hpThetaJensenSixthRectangleLower, hpThetaJensenSixthRectangleUpper,
    add_zero, show (1580 : ℝ) / 1600 = 79 / 80 by norm_num,
    show ((1580 : ℝ) + 20) / 1600 = (79 + 1) / 80 by norm_num] using h

theorem hpThetaJensen_sixthBatchIntegral_bounds (b : Fin 80) :
    hpThetaJensenSixthRectangleLower b.val ≤
        (∫ u : ℝ in Set.Ioo ((b.val : ℝ) / 80) (((b.val : ℝ) + 1) / 80),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo ((b.val : ℝ) / 80) (((b.val : ℝ) + 1) / 80),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenSixthRectangleUpper b.val := by
  fin_cases b
  · exact hpThetaJensenSixthBatch000_integral_bounds
  · exact hpThetaJensenSixthBatch001_integral_bounds
  · exact hpThetaJensenSixthBatch002_integral_bounds
  · exact hpThetaJensenSixthBatch003_integral_bounds
  · exact hpThetaJensenSixthBatch004_integral_bounds
  · exact hpThetaJensenSixthBatch005_integral_bounds
  · exact hpThetaJensenSixthBatch006_integral_bounds
  · exact hpThetaJensenSixthBatch007_integral_bounds
  · exact hpThetaJensenSixthBatch008_integral_bounds
  · exact hpThetaJensenSixthBatch009_integral_bounds
  · exact hpThetaJensenSixthBatch010_integral_bounds
  · exact hpThetaJensenSixthBatch011_integral_bounds
  · exact hpThetaJensenSixthBatch012_integral_bounds
  · exact hpThetaJensenSixthBatch013_integral_bounds
  · exact hpThetaJensenSixthBatch014_integral_bounds
  · exact hpThetaJensenSixthBatch015_integral_bounds
  · exact hpThetaJensenSixthBatch016_integral_bounds
  · exact hpThetaJensenSixthBatch017_integral_bounds
  · exact hpThetaJensenSixthBatch018_integral_bounds
  · exact hpThetaJensenSixthBatch019_integral_bounds
  · exact hpThetaJensenSixthBatch020_integral_bounds
  · exact hpThetaJensenSixthBatch021_integral_bounds
  · exact hpThetaJensenSixthBatch022_integral_bounds
  · exact hpThetaJensenSixthBatch023_integral_bounds
  · exact hpThetaJensenSixthBatch024_integral_bounds
  · exact hpThetaJensenSixthBatch025_integral_bounds
  · exact hpThetaJensenSixthBatch026_integral_bounds
  · exact hpThetaJensenSixthBatch027_integral_bounds
  · exact hpThetaJensenSixthBatch028_integral_bounds
  · exact hpThetaJensenSixthBatch029_integral_bounds
  · exact hpThetaJensenSixthBatch030_integral_bounds
  · exact hpThetaJensenSixthBatch031_integral_bounds
  · exact hpThetaJensenSixthBatch032_integral_bounds
  · exact hpThetaJensenSixthBatch033_integral_bounds
  · exact hpThetaJensenSixthBatch034_integral_bounds
  · exact hpThetaJensenSixthBatch035_integral_bounds
  · exact hpThetaJensenSixthBatch036_integral_bounds
  · exact hpThetaJensenSixthBatch037_integral_bounds
  · exact hpThetaJensenSixthBatch038_integral_bounds
  · exact hpThetaJensenSixthBatch039_integral_bounds
  · exact hpThetaJensenSixthBatch040_integral_bounds
  · exact hpThetaJensenSixthBatch041_integral_bounds
  · exact hpThetaJensenSixthBatch042_integral_bounds
  · exact hpThetaJensenSixthBatch043_integral_bounds
  · exact hpThetaJensenSixthBatch044_integral_bounds
  · exact hpThetaJensenSixthBatch045_integral_bounds
  · exact hpThetaJensenSixthBatch046_integral_bounds
  · exact hpThetaJensenSixthBatch047_integral_bounds
  · exact hpThetaJensenSixthBatch048_integral_bounds
  · exact hpThetaJensenSixthBatch049_integral_bounds
  · exact hpThetaJensenSixthBatch050_integral_bounds
  · exact hpThetaJensenSixthBatch051_integral_bounds
  · exact hpThetaJensenSixthBatch052_integral_bounds
  · exact hpThetaJensenSixthBatch053_integral_bounds
  · exact hpThetaJensenSixthBatch054_integral_bounds
  · exact hpThetaJensenSixthBatch055_integral_bounds
  · exact hpThetaJensenSixthBatch056_integral_bounds
  · exact hpThetaJensenSixthBatch057_integral_bounds
  · exact hpThetaJensenSixthBatch058_integral_bounds
  · exact hpThetaJensenSixthBatch059_integral_bounds
  · exact hpThetaJensenSixthBatch060_integral_bounds
  · exact hpThetaJensenSixthBatch061_integral_bounds
  · exact hpThetaJensenSixthBatch062_integral_bounds
  · exact hpThetaJensenSixthBatch063_integral_bounds
  · exact hpThetaJensenSixthBatch064_integral_bounds
  · exact hpThetaJensenSixthBatch065_integral_bounds
  · exact hpThetaJensenSixthBatch066_integral_bounds
  · exact hpThetaJensenSixthBatch067_integral_bounds
  · exact hpThetaJensenSixthBatch068_integral_bounds
  · exact hpThetaJensenSixthBatch069_integral_bounds
  · exact hpThetaJensenSixthBatch070_integral_bounds
  · exact hpThetaJensenSixthBatch071_integral_bounds
  · exact hpThetaJensenSixthBatch072_integral_bounds
  · exact hpThetaJensenSixthBatch073_integral_bounds
  · exact hpThetaJensenSixthBatch074_integral_bounds
  · exact hpThetaJensenSixthBatch075_integral_bounds
  · exact hpThetaJensenSixthBatch076_integral_bounds
  · exact hpThetaJensenSixthBatch077_integral_bounds
  · exact hpThetaJensenSixthBatch078_integral_bounds
  · exact hpThetaJensenSixthBatch079_integral_bounds

theorem hpThetaJensen_sixthFiniteIntegral_bounds :
    (592 / 1000000 : ℝ) ≤
        (∫ u : ℝ in Set.Ioo 0 1, u ^ 6 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo 0 1, u ^ 6 * hpRiemannThetaDifferentialKernel u) ≤
        (608 / 1000000 : ℝ) - 1 / 50000000 := by
  have hlow :
      (∑ b ∈ Finset.range 80, hpThetaJensenSixthRectangleLower b) ≤
      ∑ b ∈ Finset.range 80,
        ∫ u : ℝ in Set.Ioo ((b : ℝ) / 80) (((b : ℝ) + 1) / 80),
          u ^ 6 * hpRiemannThetaDifferentialKernel u := by
    apply Finset.sum_le_sum
    intro b hb
    exact (hpThetaJensen_sixthBatchIntegral_bounds
      ⟨b, Finset.mem_range.mp hb⟩).1
  have hupp :
      (∑ b ∈ Finset.range 80,
        ∫ u : ℝ in Set.Ioo ((b : ℝ) / 80) (((b : ℝ) + 1) / 80),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) ≤
      ∑ b ∈ Finset.range 80, hpThetaJensenSixthRectangleUpper b := by
    apply Finset.sum_le_sum
    intro b hb
    exact (hpThetaJensen_sixthBatchIntegral_bounds
      ⟨b, Finset.mem_range.mp hb⟩).2
  have hsum :
      (∑ b ∈ Finset.range 80,
        ∫ u : ℝ in Set.Ioo ((b : ℝ) / 80) (((b : ℝ) + 1) / 80),
          u ^ 6 * hpRiemannThetaDifferentialKernel u) =
      ∫ u : ℝ in Set.Ioo 0 1, u ^ 6 * hpRiemannThetaDifferentialKernel u := by
    have h := hpThetaJensen_natPowerUniformCellIntegral_sum 6 80 0
      (1 / 80) (by norm_num) (by norm_num)
    simpa only [zero_add, mul_one_div, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat,
      show (80 : ℝ) / 80 = 1 by norm_num] using h
  rw [hsum] at hlow hupp
  exact ⟨le_trans hpThetaJensen_sixthRectangle_lower_numeric hlow,
    le_trans hupp hpThetaJensen_sixthRectangle_upper_numeric⟩

theorem hpThetaJensen_sixthMoment_integral_split :
    hpThetaPhiEvenMoment 3 =
      (∫ u : ℝ in Set.Ioo 0 1, u ^ 6 * hpRiemannThetaDifferentialKernel u) +
      (∫ u : ℝ in Set.Ioi 1, u ^ 6 * hpRiemannThetaDifferentialKernel u) := by
  have h := intervalIntegral.integral_Ioi_sub_Ioi
    hpThetaPhi_sixthMoment_integrableOn (show (0 : ℝ) ≤ 1 by norm_num)
  rw [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num),
    integral_Ioc_eq_integral_Ioo] at h
  change (∫ u : ℝ in Set.Ioi 0, u ^ 6 * hpRiemannThetaDifferentialKernel u) = _
  linarith

theorem hpThetaJensen_sixthMoment_ge_certified :
    (592 / 1000000 : ℝ) ≤ hpThetaPhiEvenMoment 3 := by
  have hfin := hpThetaJensen_sixthFiniteIntegral_bounds.1
  have htail :
      0 ≤ ∫ u : ℝ in Set.Ioi 1, u ^ 6 * hpRiemannThetaDifferentialKernel u := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : 0 ≤ u := by
      change (1 : ℝ) < u at hu
      linarith
    exact mul_nonneg (pow_nonneg hu0 6)
      (le_of_lt (hpThetaPhi_pos_on_nonnegative u hu0))
  have hsplit := hpThetaJensen_sixthMoment_integral_split
  linarith

theorem hpThetaJensen_sixthMoment_le_certified :
    hpThetaPhiEvenMoment 3 ≤ (608 / 1000000 : ℝ) := by
  have hfin := hpThetaJensen_sixthFiniteIntegral_bounds.2
  have htail := hpThetaJensen_sixthMoment_tail_le_twoEminusEight
  have hsplit := hpThetaJensen_sixthMoment_integral_split
  linarith

theorem hpThetaJensen_sixthMoment_certified_bounds :
    (592 / 1000000 : ℝ) ≤ hpThetaPhiEvenMoment 3 ∧
      hpThetaPhiEvenMoment 3 ≤ (608 / 1000000 : ℝ) :=
  ⟨hpThetaJensen_sixthMoment_ge_certified, hpThetaJensen_sixthMoment_le_certified⟩

#print axioms hpThetaJensen_sixthBatchIntegral_of_kernelBounds
#print axioms hpThetaJensen_sixthBatchIntegral_bounds
#print axioms hpThetaJensen_sixthFiniteIntegral_bounds
#print axioms hpThetaJensen_sixthMoment_integral_split
#print axioms hpThetaJensen_sixthMoment_ge_certified
#print axioms hpThetaJensen_sixthMoment_le_certified
#print axioms hpThetaJensen_sixthMoment_certified_bounds
end HodgeProofHP
