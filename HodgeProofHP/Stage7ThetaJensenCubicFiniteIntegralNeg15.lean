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


theorem hpThetaJensenCubicNeg15Batch000_integral_rectangle_bounds :
    hpThetaJensenCubicNeg15RectangleLower 0 ≤
      (∫ u : ℝ in Set.Ioo (((0 : ℕ) : ℝ) / 80) ((((0 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ∧
    (∫ u : ℝ in Set.Ioo (((0 : ℕ) : ℝ) / 80) ((((0 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ≤
        hpThetaJensenCubicNeg15RectangleUpper 0 := by
  simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch000Neg15_integral_bounds

theorem hpThetaJensenCubicNeg15Batch001_integral_rectangle_bounds :
    hpThetaJensenCubicNeg15RectangleLower 1 ≤
      (∫ u : ℝ in Set.Ioo (((1 : ℕ) : ℝ) / 80) ((((1 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ∧
    (∫ u : ℝ in Set.Ioo (((1 : ℕ) : ℝ) / 80) ((((1 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ≤
        hpThetaJensenCubicNeg15RectangleUpper 1 := by
  simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch001Neg15_integral_bounds

theorem hpThetaJensenCubicNeg15Batch002_integral_rectangle_bounds :
    hpThetaJensenCubicNeg15RectangleLower 2 ≤
      (∫ u : ℝ in Set.Ioo (((2 : ℕ) : ℝ) / 80) ((((2 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ∧
    (∫ u : ℝ in Set.Ioo (((2 : ℕ) : ℝ) / 80) ((((2 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ≤
        hpThetaJensenCubicNeg15RectangleUpper 2 := by
  simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch002Neg15_integral_bounds

theorem hpThetaJensenCubicNeg15Batch003_integral_rectangle_bounds :
    hpThetaJensenCubicNeg15RectangleLower 3 ≤
      (∫ u : ℝ in Set.Ioo (((3 : ℕ) : ℝ) / 80) ((((3 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ∧
    (∫ u : ℝ in Set.Ioo (((3 : ℕ) : ℝ) / 80) ((((3 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ≤
        hpThetaJensenCubicNeg15RectangleUpper 3 := by
  simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch003Neg15_integral_bounds

theorem hpThetaJensenCubicNeg15Batch004_integral_rectangle_bounds :
    hpThetaJensenCubicNeg15RectangleLower 4 ≤
      (∫ u : ℝ in Set.Ioo (((4 : ℕ) : ℝ) / 80) ((((4 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ∧
    (∫ u : ℝ in Set.Ioo (((4 : ℕ) : ℝ) / 80) ((((4 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ≤
        hpThetaJensenCubicNeg15RectangleUpper 4 := by
  simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch004Neg15_integral_bounds

theorem hpThetaJensenCubicNeg15Batch005_integral_rectangle_bounds :
    hpThetaJensenCubicNeg15RectangleLower 5 ≤
      (∫ u : ℝ in Set.Ioo (((5 : ℕ) : ℝ) / 80) ((((5 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ∧
    (∫ u : ℝ in Set.Ioo (((5 : ℕ) : ℝ) / 80) ((((5 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ≤
        hpThetaJensenCubicNeg15RectangleUpper 5 := by
  simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch005Neg15_integral_bounds

theorem hpThetaJensenCubicNeg15Batch006_integral_rectangle_bounds :
    hpThetaJensenCubicNeg15RectangleLower 6 ≤
      (∫ u : ℝ in Set.Ioo (((6 : ℕ) : ℝ) / 80) ((((6 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ∧
    (∫ u : ℝ in Set.Ioo (((6 : ℕ) : ℝ) / 80) ((((6 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ≤
        hpThetaJensenCubicNeg15RectangleUpper 6 := by
  simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch006Neg15_integral_bounds

theorem hpThetaJensenCubicNeg15Batch007_integral_rectangle_bounds :
    hpThetaJensenCubicNeg15RectangleLower 7 ≤
      (∫ u : ℝ in Set.Ioo (((7 : ℕ) : ℝ) / 80) ((((7 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ∧
    (∫ u : ℝ in Set.Ioo (((7 : ℕ) : ℝ) / 80) ((((7 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ≤
        hpThetaJensenCubicNeg15RectangleUpper 7 := by
  simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch007Neg15_integral_bounds

theorem hpThetaJensenCubicNeg15Batch008_integral_rectangle_bounds :
    hpThetaJensenCubicNeg15RectangleLower 8 ≤
      (∫ u : ℝ in Set.Ioo (((8 : ℕ) : ℝ) / 80) ((((8 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ∧
    (∫ u : ℝ in Set.Ioo (((8 : ℕ) : ℝ) / 80) ((((8 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ≤
        hpThetaJensenCubicNeg15RectangleUpper 8 := by
  simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch008Neg15_integral_bounds

theorem hpThetaJensenCubicNeg15Batch009_integral_rectangle_bounds :
    hpThetaJensenCubicNeg15RectangleLower 9 ≤
      (∫ u : ℝ in Set.Ioo (((9 : ℕ) : ℝ) / 80) ((((9 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ∧
    (∫ u : ℝ in Set.Ioo (((9 : ℕ) : ℝ) / 80) ((((9 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ≤
        hpThetaJensenCubicNeg15RectangleUpper 9 := by
  simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch009Neg15_integral_bounds

theorem hpThetaJensenCubicNeg15Batch010_integral_rectangle_bounds :
    hpThetaJensenCubicNeg15RectangleLower 10 ≤
      (∫ u : ℝ in Set.Ioo (((10 : ℕ) : ℝ) / 80) ((((10 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ∧
    (∫ u : ℝ in Set.Ioo (((10 : ℕ) : ℝ) / 80) ((((10 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ≤
        hpThetaJensenCubicNeg15RectangleUpper 10 := by
  simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch010Neg15_integral_bounds

theorem hpThetaJensenCubicNeg15Batch011_integral_rectangle_bounds :
    hpThetaJensenCubicNeg15RectangleLower 11 ≤
      (∫ u : ℝ in Set.Ioo (((11 : ℕ) : ℝ) / 80) ((((11 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ∧
    (∫ u : ℝ in Set.Ioo (((11 : ℕ) : ℝ) / 80) ((((11 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ≤
        hpThetaJensenCubicNeg15RectangleUpper 11 := by
  simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch011Neg15_integral_bounds

theorem hpThetaJensenCubicNeg15Batch012_integral_rectangle_bounds :
    hpThetaJensenCubicNeg15RectangleLower 12 ≤
      (∫ u : ℝ in Set.Ioo (((12 : ℕ) : ℝ) / 80) ((((12 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ∧
    (∫ u : ℝ in Set.Ioo (((12 : ℕ) : ℝ) / 80) ((((12 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ≤
        hpThetaJensenCubicNeg15RectangleUpper 12 := by
  simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch012Neg15_integral_bounds

theorem hpThetaJensenCubicNeg15Batch013_integral_rectangle_bounds :
    hpThetaJensenCubicNeg15RectangleLower 13 ≤
      (∫ u : ℝ in Set.Ioo (((13 : ℕ) : ℝ) / 80) ((((13 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ∧
    (∫ u : ℝ in Set.Ioo (((13 : ℕ) : ℝ) / 80) ((((13 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ≤
        hpThetaJensenCubicNeg15RectangleUpper 13 := by
  simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch013Neg15_integral_bounds

theorem hpThetaJensenCubicNeg15Batch014_integral_rectangle_bounds :
    hpThetaJensenCubicNeg15RectangleLower 14 ≤
      (∫ u : ℝ in Set.Ioo (((14 : ℕ) : ℝ) / 80) ((((14 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ∧
    (∫ u : ℝ in Set.Ioo (((14 : ℕ) : ℝ) / 80) ((((14 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ≤
        hpThetaJensenCubicNeg15RectangleUpper 14 := by
  simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch014Neg15_integral_bounds

theorem hpThetaJensenCubicNeg15Batch015_integral_rectangle_bounds :
    hpThetaJensenCubicNeg15RectangleLower 15 ≤
      (∫ u : ℝ in Set.Ioo (((15 : ℕ) : ℝ) / 80) ((((15 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ∧
    (∫ u : ℝ in Set.Ioo (((15 : ℕ) : ℝ) / 80) ((((15 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ≤
        hpThetaJensenCubicNeg15RectangleUpper 15 := by
  simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch015Neg15_integral_bounds

theorem hpThetaJensenCubicNeg15Batch016_integral_rectangle_bounds :
    hpThetaJensenCubicNeg15RectangleLower 16 ≤
      (∫ u : ℝ in Set.Ioo (((16 : ℕ) : ℝ) / 80) ((((16 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ∧
    (∫ u : ℝ in Set.Ioo (((16 : ℕ) : ℝ) / 80) ((((16 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ≤
        hpThetaJensenCubicNeg15RectangleUpper 16 := by
  simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch016Neg15_integral_bounds

theorem hpThetaJensenCubicNeg15Batch017_integral_rectangle_bounds :
    hpThetaJensenCubicNeg15RectangleLower 17 ≤
      (∫ u : ℝ in Set.Ioo (((17 : ℕ) : ℝ) / 80) ((((17 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ∧
    (∫ u : ℝ in Set.Ioo (((17 : ℕ) : ℝ) / 80) ((((17 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ≤
        hpThetaJensenCubicNeg15RectangleUpper 17 := by
  simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch017Neg15_integral_bounds

theorem hpThetaJensenCubicNeg15Batch018_integral_rectangle_bounds :
    hpThetaJensenCubicNeg15RectangleLower 18 ≤
      (∫ u : ℝ in Set.Ioo (((18 : ℕ) : ℝ) / 80) ((((18 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ∧
    (∫ u : ℝ in Set.Ioo (((18 : ℕ) : ℝ) / 80) ((((18 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ≤
        hpThetaJensenCubicNeg15RectangleUpper 18 := by
  simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch018Neg15_integral_bounds

theorem hpThetaJensenCubicNeg15Batch019_integral_rectangle_bounds :
    hpThetaJensenCubicNeg15RectangleLower 19 ≤
      (∫ u : ℝ in Set.Ioo (((19 : ℕ) : ℝ) / 80) ((((19 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ∧
    (∫ u : ℝ in Set.Ioo (((19 : ℕ) : ℝ) / 80) ((((19 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ≤
        hpThetaJensenCubicNeg15RectangleUpper 19 := by
  simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch019Neg15_integral_bounds

theorem hpThetaJensenCubicNeg15Batch020_integral_rectangle_bounds :
    hpThetaJensenCubicNeg15RectangleLower 20 ≤
      (∫ u : ℝ in Set.Ioo (((20 : ℕ) : ℝ) / 80) ((((20 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ∧
    (∫ u : ℝ in Set.Ioo (((20 : ℕ) : ℝ) / 80) ((((20 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ≤
        hpThetaJensenCubicNeg15RectangleUpper 20 := by
  simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch020Neg15_integral_bounds

theorem hpThetaJensenCubicNeg15Batch021_integral_rectangle_bounds :
    hpThetaJensenCubicNeg15RectangleLower 21 ≤
      (∫ u : ℝ in Set.Ioo (((21 : ℕ) : ℝ) / 80) ((((21 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ∧
    (∫ u : ℝ in Set.Ioo (((21 : ℕ) : ℝ) / 80) ((((21 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ≤
        hpThetaJensenCubicNeg15RectangleUpper 21 := by
  simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch021Neg15_integral_bounds

theorem hpThetaJensenCubicNeg15Batch022_integral_rectangle_bounds :
    hpThetaJensenCubicNeg15RectangleLower 22 ≤
      (∫ u : ℝ in Set.Ioo (((22 : ℕ) : ℝ) / 80) ((((22 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ∧
    (∫ u : ℝ in Set.Ioo (((22 : ℕ) : ℝ) / 80) ((((22 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ≤
        hpThetaJensenCubicNeg15RectangleUpper 22 := by
  simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch022Neg15_integral_bounds

theorem hpThetaJensenCubicNeg15Batch023_integral_rectangle_bounds :
    hpThetaJensenCubicNeg15RectangleLower 23 ≤
      (∫ u : ℝ in Set.Ioo (((23 : ℕ) : ℝ) / 80) ((((23 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ∧
    (∫ u : ℝ in Set.Ioo (((23 : ℕ) : ℝ) / 80) ((((23 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ≤
        hpThetaJensenCubicNeg15RectangleUpper 23 := by
  simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch023Neg15_integral_bounds

theorem hpThetaJensenCubicNeg15Batch024_integral_rectangle_bounds :
    hpThetaJensenCubicNeg15RectangleLower 24 ≤
      (∫ u : ℝ in Set.Ioo (((24 : ℕ) : ℝ) / 80) ((((24 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ∧
    (∫ u : ℝ in Set.Ioo (((24 : ℕ) : ℝ) / 80) ((((24 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ≤
        hpThetaJensenCubicNeg15RectangleUpper 24 := by
  simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch024Neg15_integral_bounds

theorem hpThetaJensenCubicNeg15Batch025_integral_rectangle_bounds :
    hpThetaJensenCubicNeg15RectangleLower 25 ≤
      (∫ u : ℝ in Set.Ioo (((25 : ℕ) : ℝ) / 80) ((((25 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ∧
    (∫ u : ℝ in Set.Ioo (((25 : ℕ) : ℝ) / 80) ((((25 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ≤
        hpThetaJensenCubicNeg15RectangleUpper 25 := by
  simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch025Neg15_integral_bounds

theorem hpThetaJensenCubicNeg15Batch026_integral_rectangle_bounds :
    hpThetaJensenCubicNeg15RectangleLower 26 ≤
      (∫ u : ℝ in Set.Ioo (((26 : ℕ) : ℝ) / 80) ((((26 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ∧
    (∫ u : ℝ in Set.Ioo (((26 : ℕ) : ℝ) / 80) ((((26 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ≤
        hpThetaJensenCubicNeg15RectangleUpper 26 := by
  simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch026Neg15_integral_bounds

theorem hpThetaJensenCubicNeg15Batch027_integral_rectangle_bounds :
    hpThetaJensenCubicNeg15RectangleLower 27 ≤
      (∫ u : ℝ in Set.Ioo (((27 : ℕ) : ℝ) / 80) ((((27 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ∧
    (∫ u : ℝ in Set.Ioo (((27 : ℕ) : ℝ) / 80) ((((27 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ≤
        hpThetaJensenCubicNeg15RectangleUpper 27 := by
  simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch027Neg15_integral_bounds

theorem hpThetaJensenCubicNeg15Batch028_integral_rectangle_bounds :
    hpThetaJensenCubicNeg15RectangleLower 28 ≤
      (∫ u : ℝ in Set.Ioo (((28 : ℕ) : ℝ) / 80) ((((28 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ∧
    (∫ u : ℝ in Set.Ioo (((28 : ℕ) : ℝ) / 80) ((((28 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ≤
        hpThetaJensenCubicNeg15RectangleUpper 28 := by
  simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch028Neg15_integral_bounds

theorem hpThetaJensenCubicNeg15Batch029_integral_rectangle_bounds :
    hpThetaJensenCubicNeg15RectangleLower 29 ≤
      (∫ u : ℝ in Set.Ioo (((29 : ℕ) : ℝ) / 80) ((((29 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ∧
    (∫ u : ℝ in Set.Ioo (((29 : ℕ) : ℝ) / 80) ((((29 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ≤
        hpThetaJensenCubicNeg15RectangleUpper 29 := by
  simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch029Neg15_integral_bounds

theorem hpThetaJensenCubicNeg15Batch030_integral_rectangle_bounds :
    hpThetaJensenCubicNeg15RectangleLower 30 ≤
      (∫ u : ℝ in Set.Ioo (((30 : ℕ) : ℝ) / 80) ((((30 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ∧
    (∫ u : ℝ in Set.Ioo (((30 : ℕ) : ℝ) / 80) ((((30 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ≤
        hpThetaJensenCubicNeg15RectangleUpper 30 := by
  simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch030Neg15_integral_bounds

theorem hpThetaJensenCubicNeg15Batch031_integral_rectangle_bounds :
    hpThetaJensenCubicNeg15RectangleLower 31 ≤
      (∫ u : ℝ in Set.Ioo (((31 : ℕ) : ℝ) / 80) ((((31 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ∧
    (∫ u : ℝ in Set.Ioo (((31 : ℕ) : ℝ) / 80) ((((31 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ≤
        hpThetaJensenCubicNeg15RectangleUpper 31 := by
  simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch031Neg15_integral_bounds

theorem hpThetaJensenCubicNeg15Batch032_integral_rectangle_bounds :
    hpThetaJensenCubicNeg15RectangleLower 32 ≤
      (∫ u : ℝ in Set.Ioo (((32 : ℕ) : ℝ) / 80) ((((32 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ∧
    (∫ u : ℝ in Set.Ioo (((32 : ℕ) : ℝ) / 80) ((((32 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ≤
        hpThetaJensenCubicNeg15RectangleUpper 32 := by
  simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch032Neg15_integral_bounds

theorem hpThetaJensenCubicNeg15Batch033_integral_rectangle_bounds :
    hpThetaJensenCubicNeg15RectangleLower 33 ≤
      (∫ u : ℝ in Set.Ioo (((33 : ℕ) : ℝ) / 80) ((((33 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ∧
    (∫ u : ℝ in Set.Ioo (((33 : ℕ) : ℝ) / 80) ((((33 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ≤
        hpThetaJensenCubicNeg15RectangleUpper 33 := by
  simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch033Neg15_integral_bounds

theorem hpThetaJensenCubicNeg15Batch034_integral_rectangle_bounds :
    hpThetaJensenCubicNeg15RectangleLower 34 ≤
      (∫ u : ℝ in Set.Ioo (((34 : ℕ) : ℝ) / 80) ((((34 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ∧
    (∫ u : ℝ in Set.Ioo (((34 : ℕ) : ℝ) / 80) ((((34 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ≤
        hpThetaJensenCubicNeg15RectangleUpper 34 := by
  simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch034Neg15_integral_bounds

theorem hpThetaJensenCubicNeg15Batch035_integral_rectangle_bounds :
    hpThetaJensenCubicNeg15RectangleLower 35 ≤
      (∫ u : ℝ in Set.Ioo (((35 : ℕ) : ℝ) / 80) ((((35 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ∧
    (∫ u : ℝ in Set.Ioo (((35 : ℕ) : ℝ) / 80) ((((35 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ≤
        hpThetaJensenCubicNeg15RectangleUpper 35 := by
  simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch035Neg15_integral_bounds

theorem hpThetaJensenCubicNeg15Batch036_integral_rectangle_bounds :
    hpThetaJensenCubicNeg15RectangleLower 36 ≤
      (∫ u : ℝ in Set.Ioo (((36 : ℕ) : ℝ) / 80) ((((36 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ∧
    (∫ u : ℝ in Set.Ioo (((36 : ℕ) : ℝ) / 80) ((((36 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ≤
        hpThetaJensenCubicNeg15RectangleUpper 36 := by
  simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch036Neg15_integral_bounds

theorem hpThetaJensenCubicNeg15Batch037_integral_rectangle_bounds :
    hpThetaJensenCubicNeg15RectangleLower 37 ≤
      (∫ u : ℝ in Set.Ioo (((37 : ℕ) : ℝ) / 80) ((((37 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ∧
    (∫ u : ℝ in Set.Ioo (((37 : ℕ) : ℝ) / 80) ((((37 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ≤
        hpThetaJensenCubicNeg15RectangleUpper 37 := by
  simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch037Neg15_integral_bounds

theorem hpThetaJensenCubicNeg15Batch038_integral_rectangle_bounds :
    hpThetaJensenCubicNeg15RectangleLower 38 ≤
      (∫ u : ℝ in Set.Ioo (((38 : ℕ) : ℝ) / 80) ((((38 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ∧
    (∫ u : ℝ in Set.Ioo (((38 : ℕ) : ℝ) / 80) ((((38 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ≤
        hpThetaJensenCubicNeg15RectangleUpper 38 := by
  simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch038Neg15_integral_bounds

theorem hpThetaJensenCubicNeg15Batch039_integral_rectangle_bounds :
    hpThetaJensenCubicNeg15RectangleLower 39 ≤
      (∫ u : ℝ in Set.Ioo (((39 : ℕ) : ℝ) / 80) ((((39 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ∧
    (∫ u : ℝ in Set.Ioo (((39 : ℕ) : ℝ) / 80) ((((39 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ≤
        hpThetaJensenCubicNeg15RectangleUpper 39 := by
  simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch039Neg15_integral_bounds

theorem hpThetaJensenCubicNeg15Batch040_integral_rectangle_bounds :
    hpThetaJensenCubicNeg15RectangleLower 40 ≤
      (∫ u : ℝ in Set.Ioo (((40 : ℕ) : ℝ) / 80) ((((40 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ∧
    (∫ u : ℝ in Set.Ioo (((40 : ℕ) : ℝ) / 80) ((((40 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ≤
        hpThetaJensenCubicNeg15RectangleUpper 40 := by
  simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch040Neg15_integral_bounds

theorem hpThetaJensenCubicNeg15Batch041_integral_rectangle_bounds :
    hpThetaJensenCubicNeg15RectangleLower 41 ≤
      (∫ u : ℝ in Set.Ioo (((41 : ℕ) : ℝ) / 80) ((((41 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ∧
    (∫ u : ℝ in Set.Ioo (((41 : ℕ) : ℝ) / 80) ((((41 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ≤
        hpThetaJensenCubicNeg15RectangleUpper 41 := by
  simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch041Neg15_integral_bounds

theorem hpThetaJensenCubicNeg15Batch042_integral_rectangle_bounds :
    hpThetaJensenCubicNeg15RectangleLower 42 ≤
      (∫ u : ℝ in Set.Ioo (((42 : ℕ) : ℝ) / 80) ((((42 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ∧
    (∫ u : ℝ in Set.Ioo (((42 : ℕ) : ℝ) / 80) ((((42 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ≤
        hpThetaJensenCubicNeg15RectangleUpper 42 := by
  simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch042Neg15_integral_bounds

theorem hpThetaJensenCubicNeg15Batch043_integral_rectangle_bounds :
    hpThetaJensenCubicNeg15RectangleLower 43 ≤
      (∫ u : ℝ in Set.Ioo (((43 : ℕ) : ℝ) / 80) ((((43 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ∧
    (∫ u : ℝ in Set.Ioo (((43 : ℕ) : ℝ) / 80) ((((43 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ≤
        hpThetaJensenCubicNeg15RectangleUpper 43 := by
  simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch043Neg15_integral_bounds

theorem hpThetaJensenCubicNeg15Batch044_integral_rectangle_bounds :
    hpThetaJensenCubicNeg15RectangleLower 44 ≤
      (∫ u : ℝ in Set.Ioo (((44 : ℕ) : ℝ) / 80) ((((44 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ∧
    (∫ u : ℝ in Set.Ioo (((44 : ℕ) : ℝ) / 80) ((((44 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ≤
        hpThetaJensenCubicNeg15RectangleUpper 44 := by
  simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch044Neg15_integral_bounds

theorem hpThetaJensenCubicNeg15Batch045_integral_rectangle_bounds :
    hpThetaJensenCubicNeg15RectangleLower 45 ≤
      (∫ u : ℝ in Set.Ioo (((45 : ℕ) : ℝ) / 80) ((((45 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ∧
    (∫ u : ℝ in Set.Ioo (((45 : ℕ) : ℝ) / 80) ((((45 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ≤
        hpThetaJensenCubicNeg15RectangleUpper 45 := by
  simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch045Neg15_integral_bounds

theorem hpThetaJensenCubicNeg15Batch046_integral_rectangle_bounds :
    hpThetaJensenCubicNeg15RectangleLower 46 ≤
      (∫ u : ℝ in Set.Ioo (((46 : ℕ) : ℝ) / 80) ((((46 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ∧
    (∫ u : ℝ in Set.Ioo (((46 : ℕ) : ℝ) / 80) ((((46 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ≤
        hpThetaJensenCubicNeg15RectangleUpper 46 := by
  simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch046Neg15_integral_bounds

theorem hpThetaJensenCubicNeg15Batch047_integral_rectangle_bounds :
    hpThetaJensenCubicNeg15RectangleLower 47 ≤
      (∫ u : ℝ in Set.Ioo (((47 : ℕ) : ℝ) / 80) ((((47 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ∧
    (∫ u : ℝ in Set.Ioo (((47 : ℕ) : ℝ) / 80) ((((47 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ≤
        hpThetaJensenCubicNeg15RectangleUpper 47 := by
  simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch047Neg15_integral_bounds

theorem hpThetaJensenCubicNeg15Batch048_integral_rectangle_bounds :
    hpThetaJensenCubicNeg15RectangleLower 48 ≤
      (∫ u : ℝ in Set.Ioo (((48 : ℕ) : ℝ) / 80) ((((48 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ∧
    (∫ u : ℝ in Set.Ioo (((48 : ℕ) : ℝ) / 80) ((((48 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ≤
        hpThetaJensenCubicNeg15RectangleUpper 48 := by
  simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch048Neg15_integral_bounds

theorem hpThetaJensenCubicNeg15Batch049_integral_rectangle_bounds :
    hpThetaJensenCubicNeg15RectangleLower 49 ≤
      (∫ u : ℝ in Set.Ioo (((49 : ℕ) : ℝ) / 80) ((((49 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ∧
    (∫ u : ℝ in Set.Ioo (((49 : ℕ) : ℝ) / 80) ((((49 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ≤
        hpThetaJensenCubicNeg15RectangleUpper 49 := by
  simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch049Neg15_integral_bounds

theorem hpThetaJensenCubicNeg15Batch050_integral_rectangle_bounds :
    hpThetaJensenCubicNeg15RectangleLower 50 ≤
      (∫ u : ℝ in Set.Ioo (((50 : ℕ) : ℝ) / 80) ((((50 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ∧
    (∫ u : ℝ in Set.Ioo (((50 : ℕ) : ℝ) / 80) ((((50 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ≤
        hpThetaJensenCubicNeg15RectangleUpper 50 := by
  simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch050Neg15_integral_bounds

theorem hpThetaJensenCubicNeg15Batch051_integral_rectangle_bounds :
    hpThetaJensenCubicNeg15RectangleLower 51 ≤
      (∫ u : ℝ in Set.Ioo (((51 : ℕ) : ℝ) / 80) ((((51 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ∧
    (∫ u : ℝ in Set.Ioo (((51 : ℕ) : ℝ) / 80) ((((51 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ≤
        hpThetaJensenCubicNeg15RectangleUpper 51 := by
  simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch051Neg15_integral_bounds

theorem hpThetaJensenCubicNeg15Batch052_integral_rectangle_bounds :
    hpThetaJensenCubicNeg15RectangleLower 52 ≤
      (∫ u : ℝ in Set.Ioo (((52 : ℕ) : ℝ) / 80) ((((52 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ∧
    (∫ u : ℝ in Set.Ioo (((52 : ℕ) : ℝ) / 80) ((((52 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ≤
        hpThetaJensenCubicNeg15RectangleUpper 52 := by
  simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch052Neg15_integral_bounds

theorem hpThetaJensenCubicNeg15Batch053_integral_rectangle_bounds :
    hpThetaJensenCubicNeg15RectangleLower 53 ≤
      (∫ u : ℝ in Set.Ioo (((53 : ℕ) : ℝ) / 80) ((((53 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ∧
    (∫ u : ℝ in Set.Ioo (((53 : ℕ) : ℝ) / 80) ((((53 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ≤
        hpThetaJensenCubicNeg15RectangleUpper 53 := by
  simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch053Neg15_integral_bounds

theorem hpThetaJensenCubicNeg15Batch054_integral_rectangle_bounds :
    hpThetaJensenCubicNeg15RectangleLower 54 ≤
      (∫ u : ℝ in Set.Ioo (((54 : ℕ) : ℝ) / 80) ((((54 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ∧
    (∫ u : ℝ in Set.Ioo (((54 : ℕ) : ℝ) / 80) ((((54 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ≤
        hpThetaJensenCubicNeg15RectangleUpper 54 := by
  simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch054Neg15_integral_bounds

theorem hpThetaJensenCubicNeg15Batch055_integral_rectangle_bounds :
    hpThetaJensenCubicNeg15RectangleLower 55 ≤
      (∫ u : ℝ in Set.Ioo (((55 : ℕ) : ℝ) / 80) ((((55 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ∧
    (∫ u : ℝ in Set.Ioo (((55 : ℕ) : ℝ) / 80) ((((55 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ≤
        hpThetaJensenCubicNeg15RectangleUpper 55 := by
  simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch055Neg15_integral_bounds

theorem hpThetaJensenCubicNeg15Batch056_integral_rectangle_bounds :
    hpThetaJensenCubicNeg15RectangleLower 56 ≤
      (∫ u : ℝ in Set.Ioo (((56 : ℕ) : ℝ) / 80) ((((56 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ∧
    (∫ u : ℝ in Set.Ioo (((56 : ℕ) : ℝ) / 80) ((((56 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ≤
        hpThetaJensenCubicNeg15RectangleUpper 56 := by
  simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch056Neg15_integral_bounds

theorem hpThetaJensenCubicNeg15Batch057_integral_rectangle_bounds :
    hpThetaJensenCubicNeg15RectangleLower 57 ≤
      (∫ u : ℝ in Set.Ioo (((57 : ℕ) : ℝ) / 80) ((((57 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ∧
    (∫ u : ℝ in Set.Ioo (((57 : ℕ) : ℝ) / 80) ((((57 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ≤
        hpThetaJensenCubicNeg15RectangleUpper 57 := by
  simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch057Neg15_integral_bounds

theorem hpThetaJensenCubicNeg15Batch058_integral_rectangle_bounds :
    hpThetaJensenCubicNeg15RectangleLower 58 ≤
      (∫ u : ℝ in Set.Ioo (((58 : ℕ) : ℝ) / 80) ((((58 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ∧
    (∫ u : ℝ in Set.Ioo (((58 : ℕ) : ℝ) / 80) ((((58 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ≤
        hpThetaJensenCubicNeg15RectangleUpper 58 := by
  simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch058Neg15_integral_bounds

theorem hpThetaJensenCubicNeg15Batch059_integral_rectangle_bounds :
    hpThetaJensenCubicNeg15RectangleLower 59 ≤
      (∫ u : ℝ in Set.Ioo (((59 : ℕ) : ℝ) / 80) ((((59 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ∧
    (∫ u : ℝ in Set.Ioo (((59 : ℕ) : ℝ) / 80) ((((59 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ≤
        hpThetaJensenCubicNeg15RectangleUpper 59 := by
  simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch059Neg15_integral_bounds

theorem hpThetaJensenCubicNeg15Batch060_integral_rectangle_bounds :
    hpThetaJensenCubicNeg15RectangleLower 60 ≤
      (∫ u : ℝ in Set.Ioo (((60 : ℕ) : ℝ) / 80) ((((60 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ∧
    (∫ u : ℝ in Set.Ioo (((60 : ℕ) : ℝ) / 80) ((((60 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ≤
        hpThetaJensenCubicNeg15RectangleUpper 60 := by
  simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch060Neg15_integral_bounds

theorem hpThetaJensenCubicNeg15Batch061_integral_rectangle_bounds :
    hpThetaJensenCubicNeg15RectangleLower 61 ≤
      (∫ u : ℝ in Set.Ioo (((61 : ℕ) : ℝ) / 80) ((((61 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ∧
    (∫ u : ℝ in Set.Ioo (((61 : ℕ) : ℝ) / 80) ((((61 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ≤
        hpThetaJensenCubicNeg15RectangleUpper 61 := by
  simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch061Neg15_integral_bounds

theorem hpThetaJensenCubicNeg15Batch062_integral_rectangle_bounds :
    hpThetaJensenCubicNeg15RectangleLower 62 ≤
      (∫ u : ℝ in Set.Ioo (((62 : ℕ) : ℝ) / 80) ((((62 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ∧
    (∫ u : ℝ in Set.Ioo (((62 : ℕ) : ℝ) / 80) ((((62 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ≤
        hpThetaJensenCubicNeg15RectangleUpper 62 := by
  simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch062Neg15_integral_bounds

theorem hpThetaJensenCubicNeg15Batch063_integral_rectangle_bounds :
    hpThetaJensenCubicNeg15RectangleLower 63 ≤
      (∫ u : ℝ in Set.Ioo (((63 : ℕ) : ℝ) / 80) ((((63 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ∧
    (∫ u : ℝ in Set.Ioo (((63 : ℕ) : ℝ) / 80) ((((63 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ≤
        hpThetaJensenCubicNeg15RectangleUpper 63 := by
  simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch063Neg15_integral_bounds

theorem hpThetaJensenCubicNeg15Batch064_integral_rectangle_bounds :
    hpThetaJensenCubicNeg15RectangleLower 64 ≤
      (∫ u : ℝ in Set.Ioo (((64 : ℕ) : ℝ) / 80) ((((64 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ∧
    (∫ u : ℝ in Set.Ioo (((64 : ℕ) : ℝ) / 80) ((((64 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ≤
        hpThetaJensenCubicNeg15RectangleUpper 64 := by
  simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch064Neg15_integral_bounds

theorem hpThetaJensenCubicNeg15Batch065_integral_rectangle_bounds :
    hpThetaJensenCubicNeg15RectangleLower 65 ≤
      (∫ u : ℝ in Set.Ioo (((65 : ℕ) : ℝ) / 80) ((((65 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ∧
    (∫ u : ℝ in Set.Ioo (((65 : ℕ) : ℝ) / 80) ((((65 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ≤
        hpThetaJensenCubicNeg15RectangleUpper 65 := by
  simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch065Neg15_integral_bounds

theorem hpThetaJensenCubicNeg15Batch066_integral_rectangle_bounds :
    hpThetaJensenCubicNeg15RectangleLower 66 ≤
      (∫ u : ℝ in Set.Ioo (((66 : ℕ) : ℝ) / 80) ((((66 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ∧
    (∫ u : ℝ in Set.Ioo (((66 : ℕ) : ℝ) / 80) ((((66 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ≤
        hpThetaJensenCubicNeg15RectangleUpper 66 := by
  simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch066Neg15_integral_bounds

theorem hpThetaJensenCubicNeg15Batch067_integral_rectangle_bounds :
    hpThetaJensenCubicNeg15RectangleLower 67 ≤
      (∫ u : ℝ in Set.Ioo (((67 : ℕ) : ℝ) / 80) ((((67 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ∧
    (∫ u : ℝ in Set.Ioo (((67 : ℕ) : ℝ) / 80) ((((67 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ≤
        hpThetaJensenCubicNeg15RectangleUpper 67 := by
  simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch067Neg15_integral_bounds

theorem hpThetaJensenCubicNeg15Batch068_integral_rectangle_bounds :
    hpThetaJensenCubicNeg15RectangleLower 68 ≤
      (∫ u : ℝ in Set.Ioo (((68 : ℕ) : ℝ) / 80) ((((68 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ∧
    (∫ u : ℝ in Set.Ioo (((68 : ℕ) : ℝ) / 80) ((((68 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ≤
        hpThetaJensenCubicNeg15RectangleUpper 68 := by
  simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch068Neg15_integral_bounds

theorem hpThetaJensenCubicNeg15Batch069_integral_rectangle_bounds :
    hpThetaJensenCubicNeg15RectangleLower 69 ≤
      (∫ u : ℝ in Set.Ioo (((69 : ℕ) : ℝ) / 80) ((((69 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ∧
    (∫ u : ℝ in Set.Ioo (((69 : ℕ) : ℝ) / 80) ((((69 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ≤
        hpThetaJensenCubicNeg15RectangleUpper 69 := by
  simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch069Neg15_integral_bounds

theorem hpThetaJensenCubicNeg15Batch070_integral_rectangle_bounds :
    hpThetaJensenCubicNeg15RectangleLower 70 ≤
      (∫ u : ℝ in Set.Ioo (((70 : ℕ) : ℝ) / 80) ((((70 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ∧
    (∫ u : ℝ in Set.Ioo (((70 : ℕ) : ℝ) / 80) ((((70 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ≤
        hpThetaJensenCubicNeg15RectangleUpper 70 := by
  simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch070Neg15_integral_bounds

theorem hpThetaJensenCubicNeg15Batch071_integral_rectangle_bounds :
    hpThetaJensenCubicNeg15RectangleLower 71 ≤
      (∫ u : ℝ in Set.Ioo (((71 : ℕ) : ℝ) / 80) ((((71 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ∧
    (∫ u : ℝ in Set.Ioo (((71 : ℕ) : ℝ) / 80) ((((71 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ≤
        hpThetaJensenCubicNeg15RectangleUpper 71 := by
  simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch071Neg15_integral_bounds

theorem hpThetaJensenCubicNeg15Batch072_integral_rectangle_bounds :
    hpThetaJensenCubicNeg15RectangleLower 72 ≤
      (∫ u : ℝ in Set.Ioo (((72 : ℕ) : ℝ) / 80) ((((72 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ∧
    (∫ u : ℝ in Set.Ioo (((72 : ℕ) : ℝ) / 80) ((((72 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ≤
        hpThetaJensenCubicNeg15RectangleUpper 72 := by
  simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch072Neg15_integral_bounds

theorem hpThetaJensenCubicNeg15Batch073_integral_rectangle_bounds :
    hpThetaJensenCubicNeg15RectangleLower 73 ≤
      (∫ u : ℝ in Set.Ioo (((73 : ℕ) : ℝ) / 80) ((((73 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ∧
    (∫ u : ℝ in Set.Ioo (((73 : ℕ) : ℝ) / 80) ((((73 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ≤
        hpThetaJensenCubicNeg15RectangleUpper 73 := by
  simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch073Neg15_integral_bounds

theorem hpThetaJensenCubicNeg15Batch074_integral_rectangle_bounds :
    hpThetaJensenCubicNeg15RectangleLower 74 ≤
      (∫ u : ℝ in Set.Ioo (((74 : ℕ) : ℝ) / 80) ((((74 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ∧
    (∫ u : ℝ in Set.Ioo (((74 : ℕ) : ℝ) / 80) ((((74 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ≤
        hpThetaJensenCubicNeg15RectangleUpper 74 := by
  simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch074Neg15_integral_bounds

theorem hpThetaJensenCubicNeg15Batch075_integral_rectangle_bounds :
    hpThetaJensenCubicNeg15RectangleLower 75 ≤
      (∫ u : ℝ in Set.Ioo (((75 : ℕ) : ℝ) / 80) ((((75 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ∧
    (∫ u : ℝ in Set.Ioo (((75 : ℕ) : ℝ) / 80) ((((75 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ≤
        hpThetaJensenCubicNeg15RectangleUpper 75 := by
  simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch075Neg15_integral_bounds

theorem hpThetaJensenCubicNeg15Batch076_integral_rectangle_bounds :
    hpThetaJensenCubicNeg15RectangleLower 76 ≤
      (∫ u : ℝ in Set.Ioo (((76 : ℕ) : ℝ) / 80) ((((76 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ∧
    (∫ u : ℝ in Set.Ioo (((76 : ℕ) : ℝ) / 80) ((((76 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ≤
        hpThetaJensenCubicNeg15RectangleUpper 76 := by
  simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch076Neg15_integral_bounds

theorem hpThetaJensenCubicNeg15Batch077_integral_rectangle_bounds :
    hpThetaJensenCubicNeg15RectangleLower 77 ≤
      (∫ u : ℝ in Set.Ioo (((77 : ℕ) : ℝ) / 80) ((((77 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ∧
    (∫ u : ℝ in Set.Ioo (((77 : ℕ) : ℝ) / 80) ((((77 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ≤
        hpThetaJensenCubicNeg15RectangleUpper 77 := by
  simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch077Neg15_integral_bounds

theorem hpThetaJensenCubicNeg15Batch078_integral_rectangle_bounds :
    hpThetaJensenCubicNeg15RectangleLower 78 ≤
      (∫ u : ℝ in Set.Ioo (((78 : ℕ) : ℝ) / 80) ((((78 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ∧
    (∫ u : ℝ in Set.Ioo (((78 : ℕ) : ℝ) / 80) ((((78 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ≤
        hpThetaJensenCubicNeg15RectangleUpper 78 := by
  simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch078Neg15_integral_bounds

theorem hpThetaJensenCubicNeg15Batch079_integral_rectangle_bounds :
    hpThetaJensenCubicNeg15RectangleLower 79 ≤
      (∫ u : ℝ in Set.Ioo (((79 : ℕ) : ℝ) / 80) ((((79 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ∧
    (∫ u : ℝ in Set.Ioo (((79 : ℕ) : ℝ) / 80) ((((79 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ≤
        hpThetaJensenCubicNeg15RectangleUpper 79 := by
  simpa only [hpThetaJensenCubicNeg15RectangleLower, hpThetaJensenCubicNeg15RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch079Neg15_integral_bounds

theorem hpThetaJensenCubicNeg15_batchIntegral_rectangle_bounds (b : Fin 80) :
    hpThetaJensenCubicNeg15RectangleLower b.val ≤
      (∫ u : ℝ in Set.Ioo ((b.val : ℝ) / 80) (((b.val : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ∧
    (∫ u : ℝ in Set.Ioo ((b.val : ℝ) / 80) (((b.val : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-15) u) ≤
        hpThetaJensenCubicNeg15RectangleUpper b.val := by
  fin_cases b
  · exact hpThetaJensenCubicNeg15Batch000_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg15Batch001_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg15Batch002_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg15Batch003_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg15Batch004_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg15Batch005_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg15Batch006_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg15Batch007_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg15Batch008_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg15Batch009_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg15Batch010_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg15Batch011_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg15Batch012_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg15Batch013_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg15Batch014_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg15Batch015_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg15Batch016_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg15Batch017_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg15Batch018_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg15Batch019_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg15Batch020_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg15Batch021_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg15Batch022_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg15Batch023_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg15Batch024_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg15Batch025_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg15Batch026_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg15Batch027_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg15Batch028_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg15Batch029_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg15Batch030_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg15Batch031_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg15Batch032_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg15Batch033_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg15Batch034_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg15Batch035_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg15Batch036_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg15Batch037_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg15Batch038_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg15Batch039_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg15Batch040_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg15Batch041_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg15Batch042_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg15Batch043_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg15Batch044_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg15Batch045_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg15Batch046_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg15Batch047_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg15Batch048_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg15Batch049_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg15Batch050_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg15Batch051_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg15Batch052_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg15Batch053_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg15Batch054_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg15Batch055_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg15Batch056_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg15Batch057_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg15Batch058_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg15Batch059_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg15Batch060_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg15Batch061_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg15Batch062_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg15Batch063_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg15Batch064_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg15Batch065_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg15Batch066_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg15Batch067_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg15Batch068_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg15Batch069_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg15Batch070_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg15Batch071_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg15Batch072_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg15Batch073_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg15Batch074_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg15Batch075_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg15Batch076_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg15Batch077_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg15Batch078_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg15Batch079_integral_rectangle_bounds

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
