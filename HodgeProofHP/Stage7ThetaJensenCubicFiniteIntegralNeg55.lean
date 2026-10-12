/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenCubicBatchIntegralsNeg55
import HodgeProofHP.Stage7ThetaJensenCubicRectanglesNeg55

/-! Bounds on the finite weighted integral only. The tail and full evaluation
signs remain separate obligations. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

theorem hpThetaJensenCubicNeg55_batchIntegral_rectangle_bounds (b : Fin 80) :
    hpThetaJensenCubicNeg55RectangleLower b.val ≤
      (∫ u : ℝ in Set.Ioo ((b.val : ℝ) / 80) (((b.val : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ∧
    (∫ u : ℝ in Set.Ioo ((b.val : ℝ) / 80) (((b.val : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ≤
        hpThetaJensenCubicNeg55RectangleUpper b.val := by
  fin_cases b
  · simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch000Neg55_integral_bounds
  · simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch001Neg55_integral_bounds
  · simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch002Neg55_integral_bounds
  · simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch003Neg55_integral_bounds
  · simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch004Neg55_integral_bounds
  · simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch005Neg55_integral_bounds
  · simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch006Neg55_integral_bounds
  · simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch007Neg55_integral_bounds
  · simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch008Neg55_integral_bounds
  · simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch009Neg55_integral_bounds
  · simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch010Neg55_integral_bounds
  · simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch011Neg55_integral_bounds
  · simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch012Neg55_integral_bounds
  · simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch013Neg55_integral_bounds
  · simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch014Neg55_integral_bounds
  · simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch015Neg55_integral_bounds
  · simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch016Neg55_integral_bounds
  · simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch017Neg55_integral_bounds
  · simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch018Neg55_integral_bounds
  · simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch019Neg55_integral_bounds
  · simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch020Neg55_integral_bounds
  · simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch021Neg55_integral_bounds
  · simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch022Neg55_integral_bounds
  · simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch023Neg55_integral_bounds
  · simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch024Neg55_integral_bounds
  · simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch025Neg55_integral_bounds
  · simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch026Neg55_integral_bounds
  · simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch027Neg55_integral_bounds
  · simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch028Neg55_integral_bounds
  · simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch029Neg55_integral_bounds
  · simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch030Neg55_integral_bounds
  · simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch031Neg55_integral_bounds
  · simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch032Neg55_integral_bounds
  · simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch033Neg55_integral_bounds
  · simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch034Neg55_integral_bounds
  · simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch035Neg55_integral_bounds
  · simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch036Neg55_integral_bounds
  · simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch037Neg55_integral_bounds
  · simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch038Neg55_integral_bounds
  · simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch039Neg55_integral_bounds
  · simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch040Neg55_integral_bounds
  · simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch041Neg55_integral_bounds
  · simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch042Neg55_integral_bounds
  · simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch043Neg55_integral_bounds
  · simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch044Neg55_integral_bounds
  · simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch045Neg55_integral_bounds
  · simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch046Neg55_integral_bounds
  · simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch047Neg55_integral_bounds
  · simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch048Neg55_integral_bounds
  · simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch049Neg55_integral_bounds
  · simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch050Neg55_integral_bounds
  · simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch051Neg55_integral_bounds
  · simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch052Neg55_integral_bounds
  · simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch053Neg55_integral_bounds
  · simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch054Neg55_integral_bounds
  · simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch055Neg55_integral_bounds
  · simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch056Neg55_integral_bounds
  · simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch057Neg55_integral_bounds
  · simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch058Neg55_integral_bounds
  · simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch059Neg55_integral_bounds
  · simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch060Neg55_integral_bounds
  · simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch061Neg55_integral_bounds
  · simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch062Neg55_integral_bounds
  · simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch063Neg55_integral_bounds
  · simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch064Neg55_integral_bounds
  · simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch065Neg55_integral_bounds
  · simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch066Neg55_integral_bounds
  · simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch067Neg55_integral_bounds
  · simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch068Neg55_integral_bounds
  · simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch069Neg55_integral_bounds
  · simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch070Neg55_integral_bounds
  · simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch071Neg55_integral_bounds
  · simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch072Neg55_integral_bounds
  · simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch073Neg55_integral_bounds
  · simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch074Neg55_integral_bounds
  · simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch075Neg55_integral_bounds
  · simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch076Neg55_integral_bounds
  · simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch077Neg55_integral_bounds
  · simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch078Neg55_integral_bounds
  · simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
      hpThetaJensenCubicBatch079Neg55_integral_bounds

theorem hpThetaJensenCubicNeg55_batchIntegral_sum :
    (∑ b ∈ Finset.range 80,
      ∫ u : ℝ in Set.Ioo ((b : ℝ) / 80) (((b : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) =
      ∫ u : ℝ in Set.Ioo 0 1,
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u := by
  have h := hpThetaJensenCubic_uniformCellIntegral_sum (-55) 80 0 (1 / 80)
    (by norm_num) (by norm_num)
  have hc (b : ℕ) :
      Set.Ioo (0 + (b : ℝ) * (1 / 80))
        (0 + ((b + 1 : ℕ) : ℝ) * (1 / 80)) =
      Set.Ioo ((b : ℝ) / 80) (((b : ℝ) + 1) / 80) := by
    congr 1 <;> push_cast <;> ring
  simp_rw [hc] at h
  norm_num only [Nat.cast_ofNat, zero_add] at h
  exact h

theorem hpThetaJensenCubicNeg55_finiteIntegral_bounds :
    (6 / 1000 : ℝ) ≤
      (∫ u : ℝ in Set.Ioo 0 1,
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ∧
    (∫ u : ℝ in Set.Ioo 0 1,
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ≤
        (18 / 1000 : ℝ) := by
  have hl : (∑ b ∈ Finset.range 80, hpThetaJensenCubicNeg55RectangleLower b) ≤
      ∑ b ∈ Finset.range 80,
        ∫ u : ℝ in Set.Ioo ((b : ℝ) / 80) (((b : ℝ) + 1) / 80),
          hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u := by
    apply Finset.sum_le_sum
    intro b hb
    exact (hpThetaJensenCubicNeg55_batchIntegral_rectangle_bounds ⟨b, Finset.mem_range.mp hb⟩).1
  have hu : (∑ b ∈ Finset.range 80,
      ∫ u : ℝ in Set.Ioo ((b : ℝ) / 80) (((b : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ≤
      ∑ b ∈ Finset.range 80, hpThetaJensenCubicNeg55RectangleUpper b := by
    apply Finset.sum_le_sum
    intro b hb
    exact (hpThetaJensenCubicNeg55_batchIntegral_rectangle_bounds ⟨b, Finset.mem_range.mp hb⟩).2
  rw [hpThetaJensenCubicNeg55_batchIntegral_sum] at hl hu
  constructor
  · convert le_trans hpThetaJensenCubicNeg55_rectangle_lower_numeric hl using 1 <;> norm_num
  · convert le_trans hu hpThetaJensenCubicNeg55_rectangle_upper_numeric using 1 <;> norm_num

#print axioms hpThetaJensenCubicNeg55_batchIntegral_rectangle_bounds
#print axioms hpThetaJensenCubicNeg55_batchIntegral_sum
#print axioms hpThetaJensenCubicNeg55_finiteIntegral_bounds
end HodgeProofHP
