/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenCubicBatchIntegralsNeg42
import HodgeProofHP.Stage7ThetaJensenCubicRectanglesNeg42

/-! Bounds on the finite weighted integral only. The tail and full evaluation
signs remain separate obligations. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

theorem hpThetaJensenCubicNeg42_batchIntegral_rectangle_bounds (b : Fin 80) :
    hpThetaJensenCubicNeg42RectangleLower b.val ≤
      (∫ u : ℝ in Set.Ioo ((b.val : ℝ) / 80) (((b.val : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ∧
    (∫ u : ℝ in Set.Ioo ((b.val : ℝ) / 80) (((b.val : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ≤
        hpThetaJensenCubicNeg42RectangleUpper b.val := by
  fin_cases b
  · simpa only [Nat.cast_ofNat] using hpThetaJensenCubicBatch000Neg42_integral_bounds
  · simpa only [Nat.cast_ofNat] using hpThetaJensenCubicBatch001Neg42_integral_bounds
  · simpa only [Nat.cast_ofNat] using hpThetaJensenCubicBatch002Neg42_integral_bounds
  · simpa only [Nat.cast_ofNat] using hpThetaJensenCubicBatch003Neg42_integral_bounds
  · simpa only [Nat.cast_ofNat] using hpThetaJensenCubicBatch004Neg42_integral_bounds
  · simpa only [Nat.cast_ofNat] using hpThetaJensenCubicBatch005Neg42_integral_bounds
  · simpa only [Nat.cast_ofNat] using hpThetaJensenCubicBatch006Neg42_integral_bounds
  · simpa only [Nat.cast_ofNat] using hpThetaJensenCubicBatch007Neg42_integral_bounds
  · simpa only [Nat.cast_ofNat] using hpThetaJensenCubicBatch008Neg42_integral_bounds
  · simpa only [Nat.cast_ofNat] using hpThetaJensenCubicBatch009Neg42_integral_bounds
  · simpa only [Nat.cast_ofNat] using hpThetaJensenCubicBatch010Neg42_integral_bounds
  · simpa only [Nat.cast_ofNat] using hpThetaJensenCubicBatch011Neg42_integral_bounds
  · simpa only [Nat.cast_ofNat] using hpThetaJensenCubicBatch012Neg42_integral_bounds
  · simpa only [Nat.cast_ofNat] using hpThetaJensenCubicBatch013Neg42_integral_bounds
  · simpa only [Nat.cast_ofNat] using hpThetaJensenCubicBatch014Neg42_integral_bounds
  · simpa only [Nat.cast_ofNat] using hpThetaJensenCubicBatch015Neg42_integral_bounds
  · simpa only [Nat.cast_ofNat] using hpThetaJensenCubicBatch016Neg42_integral_bounds
  · simpa only [Nat.cast_ofNat] using hpThetaJensenCubicBatch017Neg42_integral_bounds
  · simpa only [Nat.cast_ofNat] using hpThetaJensenCubicBatch018Neg42_integral_bounds
  · simpa only [Nat.cast_ofNat] using hpThetaJensenCubicBatch019Neg42_integral_bounds
  · simpa only [Nat.cast_ofNat] using hpThetaJensenCubicBatch020Neg42_integral_bounds
  · simpa only [Nat.cast_ofNat] using hpThetaJensenCubicBatch021Neg42_integral_bounds
  · simpa only [Nat.cast_ofNat] using hpThetaJensenCubicBatch022Neg42_integral_bounds
  · simpa only [Nat.cast_ofNat] using hpThetaJensenCubicBatch023Neg42_integral_bounds
  · simpa only [Nat.cast_ofNat] using hpThetaJensenCubicBatch024Neg42_integral_bounds
  · simpa only [Nat.cast_ofNat] using hpThetaJensenCubicBatch025Neg42_integral_bounds
  · simpa only [Nat.cast_ofNat] using hpThetaJensenCubicBatch026Neg42_integral_bounds
  · simpa only [Nat.cast_ofNat] using hpThetaJensenCubicBatch027Neg42_integral_bounds
  · simpa only [Nat.cast_ofNat] using hpThetaJensenCubicBatch028Neg42_integral_bounds
  · simpa only [Nat.cast_ofNat] using hpThetaJensenCubicBatch029Neg42_integral_bounds
  · simpa only [Nat.cast_ofNat] using hpThetaJensenCubicBatch030Neg42_integral_bounds
  · simpa only [Nat.cast_ofNat] using hpThetaJensenCubicBatch031Neg42_integral_bounds
  · simpa only [Nat.cast_ofNat] using hpThetaJensenCubicBatch032Neg42_integral_bounds
  · simpa only [Nat.cast_ofNat] using hpThetaJensenCubicBatch033Neg42_integral_bounds
  · simpa only [Nat.cast_ofNat] using hpThetaJensenCubicBatch034Neg42_integral_bounds
  · simpa only [Nat.cast_ofNat] using hpThetaJensenCubicBatch035Neg42_integral_bounds
  · simpa only [Nat.cast_ofNat] using hpThetaJensenCubicBatch036Neg42_integral_bounds
  · simpa only [Nat.cast_ofNat] using hpThetaJensenCubicBatch037Neg42_integral_bounds
  · simpa only [Nat.cast_ofNat] using hpThetaJensenCubicBatch038Neg42_integral_bounds
  · simpa only [Nat.cast_ofNat] using hpThetaJensenCubicBatch039Neg42_integral_bounds
  · simpa only [Nat.cast_ofNat] using hpThetaJensenCubicBatch040Neg42_integral_bounds
  · simpa only [Nat.cast_ofNat] using hpThetaJensenCubicBatch041Neg42_integral_bounds
  · simpa only [Nat.cast_ofNat] using hpThetaJensenCubicBatch042Neg42_integral_bounds
  · simpa only [Nat.cast_ofNat] using hpThetaJensenCubicBatch043Neg42_integral_bounds
  · simpa only [Nat.cast_ofNat] using hpThetaJensenCubicBatch044Neg42_integral_bounds
  · simpa only [Nat.cast_ofNat] using hpThetaJensenCubicBatch045Neg42_integral_bounds
  · simpa only [Nat.cast_ofNat] using hpThetaJensenCubicBatch046Neg42_integral_bounds
  · simpa only [Nat.cast_ofNat] using hpThetaJensenCubicBatch047Neg42_integral_bounds
  · simpa only [Nat.cast_ofNat] using hpThetaJensenCubicBatch048Neg42_integral_bounds
  · simpa only [Nat.cast_ofNat] using hpThetaJensenCubicBatch049Neg42_integral_bounds
  · simpa only [Nat.cast_ofNat] using hpThetaJensenCubicBatch050Neg42_integral_bounds
  · simpa only [Nat.cast_ofNat] using hpThetaJensenCubicBatch051Neg42_integral_bounds
  · simpa only [Nat.cast_ofNat] using hpThetaJensenCubicBatch052Neg42_integral_bounds
  · simpa only [Nat.cast_ofNat] using hpThetaJensenCubicBatch053Neg42_integral_bounds
  · simpa only [Nat.cast_ofNat] using hpThetaJensenCubicBatch054Neg42_integral_bounds
  · simpa only [Nat.cast_ofNat] using hpThetaJensenCubicBatch055Neg42_integral_bounds
  · simpa only [Nat.cast_ofNat] using hpThetaJensenCubicBatch056Neg42_integral_bounds
  · simpa only [Nat.cast_ofNat] using hpThetaJensenCubicBatch057Neg42_integral_bounds
  · simpa only [Nat.cast_ofNat] using hpThetaJensenCubicBatch058Neg42_integral_bounds
  · simpa only [Nat.cast_ofNat] using hpThetaJensenCubicBatch059Neg42_integral_bounds
  · simpa only [Nat.cast_ofNat] using hpThetaJensenCubicBatch060Neg42_integral_bounds
  · simpa only [Nat.cast_ofNat] using hpThetaJensenCubicBatch061Neg42_integral_bounds
  · simpa only [Nat.cast_ofNat] using hpThetaJensenCubicBatch062Neg42_integral_bounds
  · simpa only [Nat.cast_ofNat] using hpThetaJensenCubicBatch063Neg42_integral_bounds
  · simpa only [Nat.cast_ofNat] using hpThetaJensenCubicBatch064Neg42_integral_bounds
  · simpa only [Nat.cast_ofNat] using hpThetaJensenCubicBatch065Neg42_integral_bounds
  · simpa only [Nat.cast_ofNat] using hpThetaJensenCubicBatch066Neg42_integral_bounds
  · simpa only [Nat.cast_ofNat] using hpThetaJensenCubicBatch067Neg42_integral_bounds
  · simpa only [Nat.cast_ofNat] using hpThetaJensenCubicBatch068Neg42_integral_bounds
  · simpa only [Nat.cast_ofNat] using hpThetaJensenCubicBatch069Neg42_integral_bounds
  · simpa only [Nat.cast_ofNat] using hpThetaJensenCubicBatch070Neg42_integral_bounds
  · simpa only [Nat.cast_ofNat] using hpThetaJensenCubicBatch071Neg42_integral_bounds
  · simpa only [Nat.cast_ofNat] using hpThetaJensenCubicBatch072Neg42_integral_bounds
  · simpa only [Nat.cast_ofNat] using hpThetaJensenCubicBatch073Neg42_integral_bounds
  · simpa only [Nat.cast_ofNat] using hpThetaJensenCubicBatch074Neg42_integral_bounds
  · simpa only [Nat.cast_ofNat] using hpThetaJensenCubicBatch075Neg42_integral_bounds
  · simpa only [Nat.cast_ofNat] using hpThetaJensenCubicBatch076Neg42_integral_bounds
  · simpa only [Nat.cast_ofNat] using hpThetaJensenCubicBatch077Neg42_integral_bounds
  · simpa only [Nat.cast_ofNat] using hpThetaJensenCubicBatch078Neg42_integral_bounds
  · simpa only [Nat.cast_ofNat] using hpThetaJensenCubicBatch079Neg42_integral_bounds

theorem hpThetaJensenCubicNeg42_batchIntegral_sum :
    (∑ b ∈ Finset.range 80,
      ∫ u : ℝ in Set.Ioo ((b : ℝ) / 80) (((b : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) =
      ∫ u : ℝ in Set.Ioo 0 1,
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u := by
  have h := hpThetaJensenCubic_uniformCellIntegral_sum (-42) 80 0 (1 / 80)
    (by norm_num) (by norm_num)
  have hc (b : ℕ) :
      Set.Ioo (0 + (b : ℝ) * (1 / 80))
        (0 + ((b + 1 : ℕ) : ℝ) * (1 / 80)) =
      Set.Ioo ((b : ℝ) / 80) (((b : ℝ) + 1) / 80) := by
    congr 1 <;> push_cast <;> ring
  simp_rw [hc] at h
  norm_num only [Nat.cast_ofNat, zero_add] at h
  exact h

theorem hpThetaJensenCubicNeg42_finiteIntegral_bounds :
    (-19 / 1000 : ℝ) ≤
      (∫ u : ℝ in Set.Ioo 0 1,
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ∧
    (∫ u : ℝ in Set.Ioo 0 1,
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ≤
        (-9 / 1000 : ℝ) := by
  have hl : (∑ b ∈ Finset.range 80, hpThetaJensenCubicNeg42RectangleLower b) ≤
      ∑ b ∈ Finset.range 80,
        ∫ u : ℝ in Set.Ioo ((b : ℝ) / 80) (((b : ℝ) + 1) / 80),
          hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u := by
    apply Finset.sum_le_sum
    intro b hb
    exact (hpThetaJensenCubicNeg42_batchIntegral_rectangle_bounds ⟨b, Finset.mem_range.mp hb⟩).1
  have hu : (∑ b ∈ Finset.range 80,
      ∫ u : ℝ in Set.Ioo ((b : ℝ) / 80) (((b : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ≤
      ∑ b ∈ Finset.range 80, hpThetaJensenCubicNeg42RectangleUpper b := by
    apply Finset.sum_le_sum
    intro b hb
    exact (hpThetaJensenCubicNeg42_batchIntegral_rectangle_bounds ⟨b, Finset.mem_range.mp hb⟩).2
  rw [hpThetaJensenCubicNeg42_batchIntegral_sum] at hl hu
  exact ⟨le_trans hpThetaJensenCubicNeg42_rectangle_lower_numeric hl,
    le_trans hu hpThetaJensenCubicNeg42_rectangle_upper_numeric⟩

#print axioms hpThetaJensenCubicNeg42_batchIntegral_rectangle_bounds
#print axioms hpThetaJensenCubicNeg42_batchIntegral_sum
#print axioms hpThetaJensenCubicNeg42_finiteIntegral_bounds
end HodgeProofHP
