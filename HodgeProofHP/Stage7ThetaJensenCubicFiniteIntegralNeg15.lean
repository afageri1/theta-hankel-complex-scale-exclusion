/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenCubicBatchIntegralsNeg15
import HodgeProofHP.Stage7ThetaJensenCubicRectanglesNeg15

/-! Bounds on the finite weighted integral only. The tail and full evaluation
signs remain separate obligations. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

theorem hpThetaJensenCubicNeg15_batchIntegral_rectangle_bounds (b : Fin 80) :
    hpThetaJensenCubicNeg15RectangleLower b.val ≤
      (∫ u : ℝ in Set.Ioo ((b.val : ℝ) / 80) (((b.val : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ∧
    (∫ u : ℝ in Set.Ioo ((b.val : ℝ) / 80) (((b.val : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ≤
        hpThetaJensenCubicNeg15RectangleUpper b.val := by
  fin_cases b
  · simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch000Neg15_integral_bounds
  · simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch001Neg15_integral_bounds
  · simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch002Neg15_integral_bounds
  · simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch003Neg15_integral_bounds
  · simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch004Neg15_integral_bounds
  · simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch005Neg15_integral_bounds
  · simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch006Neg15_integral_bounds
  · simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch007Neg15_integral_bounds
  · simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch008Neg15_integral_bounds
  · simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch009Neg15_integral_bounds
  · simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch010Neg15_integral_bounds
  · simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch011Neg15_integral_bounds
  · simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch012Neg15_integral_bounds
  · simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch013Neg15_integral_bounds
  · simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch014Neg15_integral_bounds
  · simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch015Neg15_integral_bounds
  · simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch016Neg15_integral_bounds
  · simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch017Neg15_integral_bounds
  · simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch018Neg15_integral_bounds
  · simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch019Neg15_integral_bounds
  · simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch020Neg15_integral_bounds
  · simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch021Neg15_integral_bounds
  · simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch022Neg15_integral_bounds
  · simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch023Neg15_integral_bounds
  · simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch024Neg15_integral_bounds
  · simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch025Neg15_integral_bounds
  · simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch026Neg15_integral_bounds
  · simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch027Neg15_integral_bounds
  · simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch028Neg15_integral_bounds
  · simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch029Neg15_integral_bounds
  · simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch030Neg15_integral_bounds
  · simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch031Neg15_integral_bounds
  · simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch032Neg15_integral_bounds
  · simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch033Neg15_integral_bounds
  · simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch034Neg15_integral_bounds
  · simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch035Neg15_integral_bounds
  · simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch036Neg15_integral_bounds
  · simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch037Neg15_integral_bounds
  · simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch038Neg15_integral_bounds
  · simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch039Neg15_integral_bounds
  · simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch040Neg15_integral_bounds
  · simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch041Neg15_integral_bounds
  · simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch042Neg15_integral_bounds
  · simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch043Neg15_integral_bounds
  · simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch044Neg15_integral_bounds
  · simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch045Neg15_integral_bounds
  · simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch046Neg15_integral_bounds
  · simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch047Neg15_integral_bounds
  · simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch048Neg15_integral_bounds
  · simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch049Neg15_integral_bounds
  · simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch050Neg15_integral_bounds
  · simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch051Neg15_integral_bounds
  · simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch052Neg15_integral_bounds
  · simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch053Neg15_integral_bounds
  · simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch054Neg15_integral_bounds
  · simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch055Neg15_integral_bounds
  · simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch056Neg15_integral_bounds
  · simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch057Neg15_integral_bounds
  · simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch058Neg15_integral_bounds
  · simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch059Neg15_integral_bounds
  · simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch060Neg15_integral_bounds
  · simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch061Neg15_integral_bounds
  · simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch062Neg15_integral_bounds
  · simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch063Neg15_integral_bounds
  · simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch064Neg15_integral_bounds
  · simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch065Neg15_integral_bounds
  · simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch066Neg15_integral_bounds
  · simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch067Neg15_integral_bounds
  · simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch068Neg15_integral_bounds
  · simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch069Neg15_integral_bounds
  · simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch070Neg15_integral_bounds
  · simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch071Neg15_integral_bounds
  · simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch072Neg15_integral_bounds
  · simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch073Neg15_integral_bounds
  · simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch074Neg15_integral_bounds
  · simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch075Neg15_integral_bounds
  · simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch076Neg15_integral_bounds
  · simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch077Neg15_integral_bounds
  · simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch078Neg15_integral_bounds
  · simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch079Neg15_integral_bounds

theorem hpThetaJensenCubicNeg15_batchIntegral_sum :
    (∑ b ∈ Finset.range 80,
      ∫ u : ℝ in Set.Ioo ((b : ℝ) / 80) (((b : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) =
      ∫ u : ℝ in Set.Ioo 0 1,
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u := by
  have h := hpThetaJensenCubic_uniformCellIntegral_sum (-15) 80 0 (1 / 80)
    (by norm_num) (by norm_num)
  have hc (b : ℕ) :
      Set.Ioo (0 + (b : ℝ) * (1 / 80))
        (0 + ((b + 1 : ℕ) : ℝ) * (1 / 80)) =
      Set.Ioo ((b : ℝ) / 80) (((b : ℝ) + 1) / 80) := by
    congr 1 <;> push_cast <;> ring
  simp_rw [hc] at h
  norm_num only [Nat.cast_ofNat, zero_add] at h
  exact h

theorem hpThetaJensenCubicNeg15_finiteIntegral_bounds :
    (127 / 1000 : ℝ) ≤
      (∫ u : ℝ in Set.Ioo 0 1,
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ∧
    (∫ u : ℝ in Set.Ioo 0 1,
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ≤
        (134 / 1000 : ℝ) := by
  have hl : (∑ b ∈ Finset.range 80, hpThetaJensenCubicNeg15RectangleLower b) ≤
      ∑ b ∈ Finset.range 80,
        ∫ u : ℝ in Set.Ioo ((b : ℝ) / 80) (((b : ℝ) + 1) / 80),
          hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u := by
    apply Finset.sum_le_sum
    intro b hb
    exact (hpThetaJensenCubicNeg15_batchIntegral_rectangle_bounds ⟨b, Finset.mem_range.mp hb⟩).1
  have hu : (∑ b ∈ Finset.range 80,
      ∫ u : ℝ in Set.Ioo ((b : ℝ) / 80) (((b : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ≤
      ∑ b ∈ Finset.range 80, hpThetaJensenCubicNeg15RectangleUpper b := by
    apply Finset.sum_le_sum
    intro b hb
    exact (hpThetaJensenCubicNeg15_batchIntegral_rectangle_bounds ⟨b, Finset.mem_range.mp hb⟩).2
  rw [hpThetaJensenCubicNeg15_batchIntegral_sum] at hl hu
  constructor
  · convert le_trans hpThetaJensenCubicNeg15_rectangle_lower_numeric hl using 1 <;> norm_num
  · convert le_trans hu hpThetaJensenCubicNeg15_rectangle_upper_numeric using 1 <;> norm_num

#print axioms hpThetaJensenCubicNeg15_batchIntegral_rectangle_bounds
#print axioms hpThetaJensenCubicNeg15_batchIntegral_sum
#print axioms hpThetaJensenCubicNeg15_finiteIntegral_bounds
end HodgeProofHP
