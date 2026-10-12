/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenCubicBatchIntegralsNeg90
import HodgeProofHP.Stage7ThetaJensenCubicRectanglesNeg90

/-! Bounds on the finite weighted integral only. The tail and full evaluation
signs remain separate obligations. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

theorem hpThetaJensenCubicNeg90_batchIntegral_rectangle_bounds (b : Fin 80) :
    hpThetaJensenCubicNeg90RectangleLower b.val ≤
      (∫ u : ℝ in Set.Ioo ((b.val : ℝ) / 80) (((b.val : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ∧
    (∫ u : ℝ in Set.Ioo ((b.val : ℝ) / 80) (((b.val : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ≤
        hpThetaJensenCubicNeg90RectangleUpper b.val := by
  fin_cases b
  · simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch000Neg90_integral_bounds
  · simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch001Neg90_integral_bounds
  · simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch002Neg90_integral_bounds
  · simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch003Neg90_integral_bounds
  · simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch004Neg90_integral_bounds
  · simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch005Neg90_integral_bounds
  · simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch006Neg90_integral_bounds
  · simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch007Neg90_integral_bounds
  · simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch008Neg90_integral_bounds
  · simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch009Neg90_integral_bounds
  · simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch010Neg90_integral_bounds
  · simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch011Neg90_integral_bounds
  · simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch012Neg90_integral_bounds
  · simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch013Neg90_integral_bounds
  · simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch014Neg90_integral_bounds
  · simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch015Neg90_integral_bounds
  · simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch016Neg90_integral_bounds
  · simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch017Neg90_integral_bounds
  · simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch018Neg90_integral_bounds
  · simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch019Neg90_integral_bounds
  · simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch020Neg90_integral_bounds
  · simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch021Neg90_integral_bounds
  · simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch022Neg90_integral_bounds
  · simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch023Neg90_integral_bounds
  · simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch024Neg90_integral_bounds
  · simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch025Neg90_integral_bounds
  · simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch026Neg90_integral_bounds
  · simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch027Neg90_integral_bounds
  · simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch028Neg90_integral_bounds
  · simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch029Neg90_integral_bounds
  · simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch030Neg90_integral_bounds
  · simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch031Neg90_integral_bounds
  · simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch032Neg90_integral_bounds
  · simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch033Neg90_integral_bounds
  · simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch034Neg90_integral_bounds
  · simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch035Neg90_integral_bounds
  · simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch036Neg90_integral_bounds
  · simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch037Neg90_integral_bounds
  · simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch038Neg90_integral_bounds
  · simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch039Neg90_integral_bounds
  · simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch040Neg90_integral_bounds
  · simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch041Neg90_integral_bounds
  · simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch042Neg90_integral_bounds
  · simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch043Neg90_integral_bounds
  · simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch044Neg90_integral_bounds
  · simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch045Neg90_integral_bounds
  · simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch046Neg90_integral_bounds
  · simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch047Neg90_integral_bounds
  · simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch048Neg90_integral_bounds
  · simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch049Neg90_integral_bounds
  · simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch050Neg90_integral_bounds
  · simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch051Neg90_integral_bounds
  · simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch052Neg90_integral_bounds
  · simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch053Neg90_integral_bounds
  · simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch054Neg90_integral_bounds
  · simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch055Neg90_integral_bounds
  · simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch056Neg90_integral_bounds
  · simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch057Neg90_integral_bounds
  · simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch058Neg90_integral_bounds
  · simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch059Neg90_integral_bounds
  · simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch060Neg90_integral_bounds
  · simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch061Neg90_integral_bounds
  · simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch062Neg90_integral_bounds
  · simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch063Neg90_integral_bounds
  · simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch064Neg90_integral_bounds
  · simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch065Neg90_integral_bounds
  · simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch066Neg90_integral_bounds
  · simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch067Neg90_integral_bounds
  · simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch068Neg90_integral_bounds
  · simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch069Neg90_integral_bounds
  · simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch070Neg90_integral_bounds
  · simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch071Neg90_integral_bounds
  · simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch072Neg90_integral_bounds
  · simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch073Neg90_integral_bounds
  · simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch074Neg90_integral_bounds
  · simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch075Neg90_integral_bounds
  · simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch076Neg90_integral_bounds
  · simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch077Neg90_integral_bounds
  · simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch078Neg90_integral_bounds
  · simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch079Neg90_integral_bounds

theorem hpThetaJensenCubicNeg90_batchIntegral_sum :
    (∑ b ∈ Finset.range 80,
      ∫ u : ℝ in Set.Ioo ((b : ℝ) / 80) (((b : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) =
      ∫ u : ℝ in Set.Ioo 0 1,
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u := by
  have h := hpThetaJensenCubic_uniformCellIntegral_sum (-90) 80 0 (1 / 80)
    (by norm_num) (by norm_num)
  have hc (b : ℕ) :
      Set.Ioo (0 + (b : ℝ) * (1 / 80))
        (0 + ((b + 1 : ℕ) : ℝ) * (1 / 80)) =
      Set.Ioo ((b : ℝ) / 80) (((b : ℝ) + 1) / 80) := by
    congr 1 <;> push_cast <;> ring
  simp_rw [hc] at h
  norm_num only [Nat.cast_ofNat, zero_add] at h
  exact h

theorem hpThetaJensenCubicNeg90_finiteIntegral_bounds :
    (-26 / 100 : ℝ) ≤
      (∫ u : ℝ in Set.Ioo 0 1,
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ∧
    (∫ u : ℝ in Set.Ioo 0 1,
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ≤
        (-23 / 100 : ℝ) := by
  have hl : (∑ b ∈ Finset.range 80, hpThetaJensenCubicNeg90RectangleLower b) ≤
      ∑ b ∈ Finset.range 80,
        ∫ u : ℝ in Set.Ioo ((b : ℝ) / 80) (((b : ℝ) + 1) / 80),
          hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u := by
    apply Finset.sum_le_sum
    intro b hb
    exact (hpThetaJensenCubicNeg90_batchIntegral_rectangle_bounds ⟨b, Finset.mem_range.mp hb⟩).1
  have hu : (∑ b ∈ Finset.range 80,
      ∫ u : ℝ in Set.Ioo ((b : ℝ) / 80) (((b : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ≤
      ∑ b ∈ Finset.range 80, hpThetaJensenCubicNeg90RectangleUpper b := by
    apply Finset.sum_le_sum
    intro b hb
    exact (hpThetaJensenCubicNeg90_batchIntegral_rectangle_bounds ⟨b, Finset.mem_range.mp hb⟩).2
  rw [hpThetaJensenCubicNeg90_batchIntegral_sum] at hl hu
  constructor
  · convert le_trans hpThetaJensenCubicNeg90_rectangle_lower_numeric hl using 1 <;> norm_num
  · convert le_trans hu hpThetaJensenCubicNeg90_rectangle_upper_numeric using 1 <;> norm_num

#print axioms hpThetaJensenCubicNeg90_batchIntegral_rectangle_bounds
#print axioms hpThetaJensenCubicNeg90_batchIntegral_sum
#print axioms hpThetaJensenCubicNeg90_finiteIntegral_bounds
end HodgeProofHP
