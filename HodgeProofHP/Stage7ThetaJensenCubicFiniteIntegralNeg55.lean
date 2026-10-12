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


theorem hpThetaJensenCubicNeg55Batch000_integral_rectangle_bounds :
    hpThetaJensenCubicNeg55RectangleLower 0 ≤
      (∫ u : ℝ in Set.Ioo (((0 : ℕ) : ℝ) / 80) ((((0 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ∧
    (∫ u : ℝ in Set.Ioo (((0 : ℕ) : ℝ) / 80) ((((0 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ≤
        hpThetaJensenCubicNeg55RectangleUpper 0 := by
  simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch000Neg55_integral_bounds

theorem hpThetaJensenCubicNeg55Batch001_integral_rectangle_bounds :
    hpThetaJensenCubicNeg55RectangleLower 1 ≤
      (∫ u : ℝ in Set.Ioo (((1 : ℕ) : ℝ) / 80) ((((1 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ∧
    (∫ u : ℝ in Set.Ioo (((1 : ℕ) : ℝ) / 80) ((((1 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ≤
        hpThetaJensenCubicNeg55RectangleUpper 1 := by
  simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch001Neg55_integral_bounds

theorem hpThetaJensenCubicNeg55Batch002_integral_rectangle_bounds :
    hpThetaJensenCubicNeg55RectangleLower 2 ≤
      (∫ u : ℝ in Set.Ioo (((2 : ℕ) : ℝ) / 80) ((((2 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ∧
    (∫ u : ℝ in Set.Ioo (((2 : ℕ) : ℝ) / 80) ((((2 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ≤
        hpThetaJensenCubicNeg55RectangleUpper 2 := by
  simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch002Neg55_integral_bounds

theorem hpThetaJensenCubicNeg55Batch003_integral_rectangle_bounds :
    hpThetaJensenCubicNeg55RectangleLower 3 ≤
      (∫ u : ℝ in Set.Ioo (((3 : ℕ) : ℝ) / 80) ((((3 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ∧
    (∫ u : ℝ in Set.Ioo (((3 : ℕ) : ℝ) / 80) ((((3 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ≤
        hpThetaJensenCubicNeg55RectangleUpper 3 := by
  simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch003Neg55_integral_bounds

theorem hpThetaJensenCubicNeg55Batch004_integral_rectangle_bounds :
    hpThetaJensenCubicNeg55RectangleLower 4 ≤
      (∫ u : ℝ in Set.Ioo (((4 : ℕ) : ℝ) / 80) ((((4 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ∧
    (∫ u : ℝ in Set.Ioo (((4 : ℕ) : ℝ) / 80) ((((4 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ≤
        hpThetaJensenCubicNeg55RectangleUpper 4 := by
  simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch004Neg55_integral_bounds

theorem hpThetaJensenCubicNeg55Batch005_integral_rectangle_bounds :
    hpThetaJensenCubicNeg55RectangleLower 5 ≤
      (∫ u : ℝ in Set.Ioo (((5 : ℕ) : ℝ) / 80) ((((5 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ∧
    (∫ u : ℝ in Set.Ioo (((5 : ℕ) : ℝ) / 80) ((((5 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ≤
        hpThetaJensenCubicNeg55RectangleUpper 5 := by
  simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch005Neg55_integral_bounds

theorem hpThetaJensenCubicNeg55Batch006_integral_rectangle_bounds :
    hpThetaJensenCubicNeg55RectangleLower 6 ≤
      (∫ u : ℝ in Set.Ioo (((6 : ℕ) : ℝ) / 80) ((((6 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ∧
    (∫ u : ℝ in Set.Ioo (((6 : ℕ) : ℝ) / 80) ((((6 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ≤
        hpThetaJensenCubicNeg55RectangleUpper 6 := by
  simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch006Neg55_integral_bounds

theorem hpThetaJensenCubicNeg55Batch007_integral_rectangle_bounds :
    hpThetaJensenCubicNeg55RectangleLower 7 ≤
      (∫ u : ℝ in Set.Ioo (((7 : ℕ) : ℝ) / 80) ((((7 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ∧
    (∫ u : ℝ in Set.Ioo (((7 : ℕ) : ℝ) / 80) ((((7 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ≤
        hpThetaJensenCubicNeg55RectangleUpper 7 := by
  simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch007Neg55_integral_bounds

theorem hpThetaJensenCubicNeg55Batch008_integral_rectangle_bounds :
    hpThetaJensenCubicNeg55RectangleLower 8 ≤
      (∫ u : ℝ in Set.Ioo (((8 : ℕ) : ℝ) / 80) ((((8 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ∧
    (∫ u : ℝ in Set.Ioo (((8 : ℕ) : ℝ) / 80) ((((8 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ≤
        hpThetaJensenCubicNeg55RectangleUpper 8 := by
  simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch008Neg55_integral_bounds

theorem hpThetaJensenCubicNeg55Batch009_integral_rectangle_bounds :
    hpThetaJensenCubicNeg55RectangleLower 9 ≤
      (∫ u : ℝ in Set.Ioo (((9 : ℕ) : ℝ) / 80) ((((9 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ∧
    (∫ u : ℝ in Set.Ioo (((9 : ℕ) : ℝ) / 80) ((((9 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ≤
        hpThetaJensenCubicNeg55RectangleUpper 9 := by
  simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch009Neg55_integral_bounds

theorem hpThetaJensenCubicNeg55Batch010_integral_rectangle_bounds :
    hpThetaJensenCubicNeg55RectangleLower 10 ≤
      (∫ u : ℝ in Set.Ioo (((10 : ℕ) : ℝ) / 80) ((((10 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ∧
    (∫ u : ℝ in Set.Ioo (((10 : ℕ) : ℝ) / 80) ((((10 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ≤
        hpThetaJensenCubicNeg55RectangleUpper 10 := by
  simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch010Neg55_integral_bounds

theorem hpThetaJensenCubicNeg55Batch011_integral_rectangle_bounds :
    hpThetaJensenCubicNeg55RectangleLower 11 ≤
      (∫ u : ℝ in Set.Ioo (((11 : ℕ) : ℝ) / 80) ((((11 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ∧
    (∫ u : ℝ in Set.Ioo (((11 : ℕ) : ℝ) / 80) ((((11 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ≤
        hpThetaJensenCubicNeg55RectangleUpper 11 := by
  simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch011Neg55_integral_bounds

theorem hpThetaJensenCubicNeg55Batch012_integral_rectangle_bounds :
    hpThetaJensenCubicNeg55RectangleLower 12 ≤
      (∫ u : ℝ in Set.Ioo (((12 : ℕ) : ℝ) / 80) ((((12 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ∧
    (∫ u : ℝ in Set.Ioo (((12 : ℕ) : ℝ) / 80) ((((12 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ≤
        hpThetaJensenCubicNeg55RectangleUpper 12 := by
  simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch012Neg55_integral_bounds

theorem hpThetaJensenCubicNeg55Batch013_integral_rectangle_bounds :
    hpThetaJensenCubicNeg55RectangleLower 13 ≤
      (∫ u : ℝ in Set.Ioo (((13 : ℕ) : ℝ) / 80) ((((13 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ∧
    (∫ u : ℝ in Set.Ioo (((13 : ℕ) : ℝ) / 80) ((((13 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ≤
        hpThetaJensenCubicNeg55RectangleUpper 13 := by
  simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch013Neg55_integral_bounds

theorem hpThetaJensenCubicNeg55Batch014_integral_rectangle_bounds :
    hpThetaJensenCubicNeg55RectangleLower 14 ≤
      (∫ u : ℝ in Set.Ioo (((14 : ℕ) : ℝ) / 80) ((((14 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ∧
    (∫ u : ℝ in Set.Ioo (((14 : ℕ) : ℝ) / 80) ((((14 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ≤
        hpThetaJensenCubicNeg55RectangleUpper 14 := by
  simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch014Neg55_integral_bounds

theorem hpThetaJensenCubicNeg55Batch015_integral_rectangle_bounds :
    hpThetaJensenCubicNeg55RectangleLower 15 ≤
      (∫ u : ℝ in Set.Ioo (((15 : ℕ) : ℝ) / 80) ((((15 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ∧
    (∫ u : ℝ in Set.Ioo (((15 : ℕ) : ℝ) / 80) ((((15 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ≤
        hpThetaJensenCubicNeg55RectangleUpper 15 := by
  simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch015Neg55_integral_bounds

theorem hpThetaJensenCubicNeg55Batch016_integral_rectangle_bounds :
    hpThetaJensenCubicNeg55RectangleLower 16 ≤
      (∫ u : ℝ in Set.Ioo (((16 : ℕ) : ℝ) / 80) ((((16 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ∧
    (∫ u : ℝ in Set.Ioo (((16 : ℕ) : ℝ) / 80) ((((16 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ≤
        hpThetaJensenCubicNeg55RectangleUpper 16 := by
  simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch016Neg55_integral_bounds

theorem hpThetaJensenCubicNeg55Batch017_integral_rectangle_bounds :
    hpThetaJensenCubicNeg55RectangleLower 17 ≤
      (∫ u : ℝ in Set.Ioo (((17 : ℕ) : ℝ) / 80) ((((17 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ∧
    (∫ u : ℝ in Set.Ioo (((17 : ℕ) : ℝ) / 80) ((((17 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ≤
        hpThetaJensenCubicNeg55RectangleUpper 17 := by
  simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch017Neg55_integral_bounds

theorem hpThetaJensenCubicNeg55Batch018_integral_rectangle_bounds :
    hpThetaJensenCubicNeg55RectangleLower 18 ≤
      (∫ u : ℝ in Set.Ioo (((18 : ℕ) : ℝ) / 80) ((((18 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ∧
    (∫ u : ℝ in Set.Ioo (((18 : ℕ) : ℝ) / 80) ((((18 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ≤
        hpThetaJensenCubicNeg55RectangleUpper 18 := by
  simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch018Neg55_integral_bounds

theorem hpThetaJensenCubicNeg55Batch019_integral_rectangle_bounds :
    hpThetaJensenCubicNeg55RectangleLower 19 ≤
      (∫ u : ℝ in Set.Ioo (((19 : ℕ) : ℝ) / 80) ((((19 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ∧
    (∫ u : ℝ in Set.Ioo (((19 : ℕ) : ℝ) / 80) ((((19 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ≤
        hpThetaJensenCubicNeg55RectangleUpper 19 := by
  simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch019Neg55_integral_bounds

theorem hpThetaJensenCubicNeg55Batch020_integral_rectangle_bounds :
    hpThetaJensenCubicNeg55RectangleLower 20 ≤
      (∫ u : ℝ in Set.Ioo (((20 : ℕ) : ℝ) / 80) ((((20 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ∧
    (∫ u : ℝ in Set.Ioo (((20 : ℕ) : ℝ) / 80) ((((20 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ≤
        hpThetaJensenCubicNeg55RectangleUpper 20 := by
  simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch020Neg55_integral_bounds

theorem hpThetaJensenCubicNeg55Batch021_integral_rectangle_bounds :
    hpThetaJensenCubicNeg55RectangleLower 21 ≤
      (∫ u : ℝ in Set.Ioo (((21 : ℕ) : ℝ) / 80) ((((21 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ∧
    (∫ u : ℝ in Set.Ioo (((21 : ℕ) : ℝ) / 80) ((((21 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ≤
        hpThetaJensenCubicNeg55RectangleUpper 21 := by
  simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch021Neg55_integral_bounds

theorem hpThetaJensenCubicNeg55Batch022_integral_rectangle_bounds :
    hpThetaJensenCubicNeg55RectangleLower 22 ≤
      (∫ u : ℝ in Set.Ioo (((22 : ℕ) : ℝ) / 80) ((((22 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ∧
    (∫ u : ℝ in Set.Ioo (((22 : ℕ) : ℝ) / 80) ((((22 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ≤
        hpThetaJensenCubicNeg55RectangleUpper 22 := by
  simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch022Neg55_integral_bounds

theorem hpThetaJensenCubicNeg55Batch023_integral_rectangle_bounds :
    hpThetaJensenCubicNeg55RectangleLower 23 ≤
      (∫ u : ℝ in Set.Ioo (((23 : ℕ) : ℝ) / 80) ((((23 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ∧
    (∫ u : ℝ in Set.Ioo (((23 : ℕ) : ℝ) / 80) ((((23 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ≤
        hpThetaJensenCubicNeg55RectangleUpper 23 := by
  simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch023Neg55_integral_bounds

theorem hpThetaJensenCubicNeg55Batch024_integral_rectangle_bounds :
    hpThetaJensenCubicNeg55RectangleLower 24 ≤
      (∫ u : ℝ in Set.Ioo (((24 : ℕ) : ℝ) / 80) ((((24 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ∧
    (∫ u : ℝ in Set.Ioo (((24 : ℕ) : ℝ) / 80) ((((24 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ≤
        hpThetaJensenCubicNeg55RectangleUpper 24 := by
  simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch024Neg55_integral_bounds

theorem hpThetaJensenCubicNeg55Batch025_integral_rectangle_bounds :
    hpThetaJensenCubicNeg55RectangleLower 25 ≤
      (∫ u : ℝ in Set.Ioo (((25 : ℕ) : ℝ) / 80) ((((25 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ∧
    (∫ u : ℝ in Set.Ioo (((25 : ℕ) : ℝ) / 80) ((((25 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ≤
        hpThetaJensenCubicNeg55RectangleUpper 25 := by
  simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch025Neg55_integral_bounds

theorem hpThetaJensenCubicNeg55Batch026_integral_rectangle_bounds :
    hpThetaJensenCubicNeg55RectangleLower 26 ≤
      (∫ u : ℝ in Set.Ioo (((26 : ℕ) : ℝ) / 80) ((((26 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ∧
    (∫ u : ℝ in Set.Ioo (((26 : ℕ) : ℝ) / 80) ((((26 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ≤
        hpThetaJensenCubicNeg55RectangleUpper 26 := by
  simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch026Neg55_integral_bounds

theorem hpThetaJensenCubicNeg55Batch027_integral_rectangle_bounds :
    hpThetaJensenCubicNeg55RectangleLower 27 ≤
      (∫ u : ℝ in Set.Ioo (((27 : ℕ) : ℝ) / 80) ((((27 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ∧
    (∫ u : ℝ in Set.Ioo (((27 : ℕ) : ℝ) / 80) ((((27 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ≤
        hpThetaJensenCubicNeg55RectangleUpper 27 := by
  simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch027Neg55_integral_bounds

theorem hpThetaJensenCubicNeg55Batch028_integral_rectangle_bounds :
    hpThetaJensenCubicNeg55RectangleLower 28 ≤
      (∫ u : ℝ in Set.Ioo (((28 : ℕ) : ℝ) / 80) ((((28 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ∧
    (∫ u : ℝ in Set.Ioo (((28 : ℕ) : ℝ) / 80) ((((28 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ≤
        hpThetaJensenCubicNeg55RectangleUpper 28 := by
  simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch028Neg55_integral_bounds

theorem hpThetaJensenCubicNeg55Batch029_integral_rectangle_bounds :
    hpThetaJensenCubicNeg55RectangleLower 29 ≤
      (∫ u : ℝ in Set.Ioo (((29 : ℕ) : ℝ) / 80) ((((29 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ∧
    (∫ u : ℝ in Set.Ioo (((29 : ℕ) : ℝ) / 80) ((((29 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ≤
        hpThetaJensenCubicNeg55RectangleUpper 29 := by
  simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch029Neg55_integral_bounds

theorem hpThetaJensenCubicNeg55Batch030_integral_rectangle_bounds :
    hpThetaJensenCubicNeg55RectangleLower 30 ≤
      (∫ u : ℝ in Set.Ioo (((30 : ℕ) : ℝ) / 80) ((((30 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ∧
    (∫ u : ℝ in Set.Ioo (((30 : ℕ) : ℝ) / 80) ((((30 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ≤
        hpThetaJensenCubicNeg55RectangleUpper 30 := by
  simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch030Neg55_integral_bounds

theorem hpThetaJensenCubicNeg55Batch031_integral_rectangle_bounds :
    hpThetaJensenCubicNeg55RectangleLower 31 ≤
      (∫ u : ℝ in Set.Ioo (((31 : ℕ) : ℝ) / 80) ((((31 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ∧
    (∫ u : ℝ in Set.Ioo (((31 : ℕ) : ℝ) / 80) ((((31 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ≤
        hpThetaJensenCubicNeg55RectangleUpper 31 := by
  simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch031Neg55_integral_bounds

theorem hpThetaJensenCubicNeg55Batch032_integral_rectangle_bounds :
    hpThetaJensenCubicNeg55RectangleLower 32 ≤
      (∫ u : ℝ in Set.Ioo (((32 : ℕ) : ℝ) / 80) ((((32 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ∧
    (∫ u : ℝ in Set.Ioo (((32 : ℕ) : ℝ) / 80) ((((32 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ≤
        hpThetaJensenCubicNeg55RectangleUpper 32 := by
  simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch032Neg55_integral_bounds

theorem hpThetaJensenCubicNeg55Batch033_integral_rectangle_bounds :
    hpThetaJensenCubicNeg55RectangleLower 33 ≤
      (∫ u : ℝ in Set.Ioo (((33 : ℕ) : ℝ) / 80) ((((33 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ∧
    (∫ u : ℝ in Set.Ioo (((33 : ℕ) : ℝ) / 80) ((((33 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ≤
        hpThetaJensenCubicNeg55RectangleUpper 33 := by
  simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch033Neg55_integral_bounds

theorem hpThetaJensenCubicNeg55Batch034_integral_rectangle_bounds :
    hpThetaJensenCubicNeg55RectangleLower 34 ≤
      (∫ u : ℝ in Set.Ioo (((34 : ℕ) : ℝ) / 80) ((((34 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ∧
    (∫ u : ℝ in Set.Ioo (((34 : ℕ) : ℝ) / 80) ((((34 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ≤
        hpThetaJensenCubicNeg55RectangleUpper 34 := by
  simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch034Neg55_integral_bounds

theorem hpThetaJensenCubicNeg55Batch035_integral_rectangle_bounds :
    hpThetaJensenCubicNeg55RectangleLower 35 ≤
      (∫ u : ℝ in Set.Ioo (((35 : ℕ) : ℝ) / 80) ((((35 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ∧
    (∫ u : ℝ in Set.Ioo (((35 : ℕ) : ℝ) / 80) ((((35 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ≤
        hpThetaJensenCubicNeg55RectangleUpper 35 := by
  simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch035Neg55_integral_bounds

theorem hpThetaJensenCubicNeg55Batch036_integral_rectangle_bounds :
    hpThetaJensenCubicNeg55RectangleLower 36 ≤
      (∫ u : ℝ in Set.Ioo (((36 : ℕ) : ℝ) / 80) ((((36 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ∧
    (∫ u : ℝ in Set.Ioo (((36 : ℕ) : ℝ) / 80) ((((36 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ≤
        hpThetaJensenCubicNeg55RectangleUpper 36 := by
  simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch036Neg55_integral_bounds

theorem hpThetaJensenCubicNeg55Batch037_integral_rectangle_bounds :
    hpThetaJensenCubicNeg55RectangleLower 37 ≤
      (∫ u : ℝ in Set.Ioo (((37 : ℕ) : ℝ) / 80) ((((37 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ∧
    (∫ u : ℝ in Set.Ioo (((37 : ℕ) : ℝ) / 80) ((((37 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ≤
        hpThetaJensenCubicNeg55RectangleUpper 37 := by
  simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch037Neg55_integral_bounds

theorem hpThetaJensenCubicNeg55Batch038_integral_rectangle_bounds :
    hpThetaJensenCubicNeg55RectangleLower 38 ≤
      (∫ u : ℝ in Set.Ioo (((38 : ℕ) : ℝ) / 80) ((((38 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ∧
    (∫ u : ℝ in Set.Ioo (((38 : ℕ) : ℝ) / 80) ((((38 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ≤
        hpThetaJensenCubicNeg55RectangleUpper 38 := by
  simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch038Neg55_integral_bounds

theorem hpThetaJensenCubicNeg55Batch039_integral_rectangle_bounds :
    hpThetaJensenCubicNeg55RectangleLower 39 ≤
      (∫ u : ℝ in Set.Ioo (((39 : ℕ) : ℝ) / 80) ((((39 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ∧
    (∫ u : ℝ in Set.Ioo (((39 : ℕ) : ℝ) / 80) ((((39 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ≤
        hpThetaJensenCubicNeg55RectangleUpper 39 := by
  simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch039Neg55_integral_bounds

theorem hpThetaJensenCubicNeg55Batch040_integral_rectangle_bounds :
    hpThetaJensenCubicNeg55RectangleLower 40 ≤
      (∫ u : ℝ in Set.Ioo (((40 : ℕ) : ℝ) / 80) ((((40 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ∧
    (∫ u : ℝ in Set.Ioo (((40 : ℕ) : ℝ) / 80) ((((40 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ≤
        hpThetaJensenCubicNeg55RectangleUpper 40 := by
  simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch040Neg55_integral_bounds

theorem hpThetaJensenCubicNeg55Batch041_integral_rectangle_bounds :
    hpThetaJensenCubicNeg55RectangleLower 41 ≤
      (∫ u : ℝ in Set.Ioo (((41 : ℕ) : ℝ) / 80) ((((41 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ∧
    (∫ u : ℝ in Set.Ioo (((41 : ℕ) : ℝ) / 80) ((((41 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ≤
        hpThetaJensenCubicNeg55RectangleUpper 41 := by
  simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch041Neg55_integral_bounds

theorem hpThetaJensenCubicNeg55Batch042_integral_rectangle_bounds :
    hpThetaJensenCubicNeg55RectangleLower 42 ≤
      (∫ u : ℝ in Set.Ioo (((42 : ℕ) : ℝ) / 80) ((((42 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ∧
    (∫ u : ℝ in Set.Ioo (((42 : ℕ) : ℝ) / 80) ((((42 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ≤
        hpThetaJensenCubicNeg55RectangleUpper 42 := by
  simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch042Neg55_integral_bounds

theorem hpThetaJensenCubicNeg55Batch043_integral_rectangle_bounds :
    hpThetaJensenCubicNeg55RectangleLower 43 ≤
      (∫ u : ℝ in Set.Ioo (((43 : ℕ) : ℝ) / 80) ((((43 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ∧
    (∫ u : ℝ in Set.Ioo (((43 : ℕ) : ℝ) / 80) ((((43 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ≤
        hpThetaJensenCubicNeg55RectangleUpper 43 := by
  simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch043Neg55_integral_bounds

theorem hpThetaJensenCubicNeg55Batch044_integral_rectangle_bounds :
    hpThetaJensenCubicNeg55RectangleLower 44 ≤
      (∫ u : ℝ in Set.Ioo (((44 : ℕ) : ℝ) / 80) ((((44 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ∧
    (∫ u : ℝ in Set.Ioo (((44 : ℕ) : ℝ) / 80) ((((44 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ≤
        hpThetaJensenCubicNeg55RectangleUpper 44 := by
  simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch044Neg55_integral_bounds

theorem hpThetaJensenCubicNeg55Batch045_integral_rectangle_bounds :
    hpThetaJensenCubicNeg55RectangleLower 45 ≤
      (∫ u : ℝ in Set.Ioo (((45 : ℕ) : ℝ) / 80) ((((45 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ∧
    (∫ u : ℝ in Set.Ioo (((45 : ℕ) : ℝ) / 80) ((((45 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ≤
        hpThetaJensenCubicNeg55RectangleUpper 45 := by
  simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch045Neg55_integral_bounds

theorem hpThetaJensenCubicNeg55Batch046_integral_rectangle_bounds :
    hpThetaJensenCubicNeg55RectangleLower 46 ≤
      (∫ u : ℝ in Set.Ioo (((46 : ℕ) : ℝ) / 80) ((((46 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ∧
    (∫ u : ℝ in Set.Ioo (((46 : ℕ) : ℝ) / 80) ((((46 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ≤
        hpThetaJensenCubicNeg55RectangleUpper 46 := by
  simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch046Neg55_integral_bounds

theorem hpThetaJensenCubicNeg55Batch047_integral_rectangle_bounds :
    hpThetaJensenCubicNeg55RectangleLower 47 ≤
      (∫ u : ℝ in Set.Ioo (((47 : ℕ) : ℝ) / 80) ((((47 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ∧
    (∫ u : ℝ in Set.Ioo (((47 : ℕ) : ℝ) / 80) ((((47 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ≤
        hpThetaJensenCubicNeg55RectangleUpper 47 := by
  simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch047Neg55_integral_bounds

theorem hpThetaJensenCubicNeg55Batch048_integral_rectangle_bounds :
    hpThetaJensenCubicNeg55RectangleLower 48 ≤
      (∫ u : ℝ in Set.Ioo (((48 : ℕ) : ℝ) / 80) ((((48 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ∧
    (∫ u : ℝ in Set.Ioo (((48 : ℕ) : ℝ) / 80) ((((48 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ≤
        hpThetaJensenCubicNeg55RectangleUpper 48 := by
  simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch048Neg55_integral_bounds

theorem hpThetaJensenCubicNeg55Batch049_integral_rectangle_bounds :
    hpThetaJensenCubicNeg55RectangleLower 49 ≤
      (∫ u : ℝ in Set.Ioo (((49 : ℕ) : ℝ) / 80) ((((49 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ∧
    (∫ u : ℝ in Set.Ioo (((49 : ℕ) : ℝ) / 80) ((((49 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ≤
        hpThetaJensenCubicNeg55RectangleUpper 49 := by
  simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch049Neg55_integral_bounds

theorem hpThetaJensenCubicNeg55Batch050_integral_rectangle_bounds :
    hpThetaJensenCubicNeg55RectangleLower 50 ≤
      (∫ u : ℝ in Set.Ioo (((50 : ℕ) : ℝ) / 80) ((((50 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ∧
    (∫ u : ℝ in Set.Ioo (((50 : ℕ) : ℝ) / 80) ((((50 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ≤
        hpThetaJensenCubicNeg55RectangleUpper 50 := by
  simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch050Neg55_integral_bounds

theorem hpThetaJensenCubicNeg55Batch051_integral_rectangle_bounds :
    hpThetaJensenCubicNeg55RectangleLower 51 ≤
      (∫ u : ℝ in Set.Ioo (((51 : ℕ) : ℝ) / 80) ((((51 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ∧
    (∫ u : ℝ in Set.Ioo (((51 : ℕ) : ℝ) / 80) ((((51 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ≤
        hpThetaJensenCubicNeg55RectangleUpper 51 := by
  simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch051Neg55_integral_bounds

theorem hpThetaJensenCubicNeg55Batch052_integral_rectangle_bounds :
    hpThetaJensenCubicNeg55RectangleLower 52 ≤
      (∫ u : ℝ in Set.Ioo (((52 : ℕ) : ℝ) / 80) ((((52 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ∧
    (∫ u : ℝ in Set.Ioo (((52 : ℕ) : ℝ) / 80) ((((52 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ≤
        hpThetaJensenCubicNeg55RectangleUpper 52 := by
  simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch052Neg55_integral_bounds

theorem hpThetaJensenCubicNeg55Batch053_integral_rectangle_bounds :
    hpThetaJensenCubicNeg55RectangleLower 53 ≤
      (∫ u : ℝ in Set.Ioo (((53 : ℕ) : ℝ) / 80) ((((53 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ∧
    (∫ u : ℝ in Set.Ioo (((53 : ℕ) : ℝ) / 80) ((((53 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ≤
        hpThetaJensenCubicNeg55RectangleUpper 53 := by
  simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch053Neg55_integral_bounds

theorem hpThetaJensenCubicNeg55Batch054_integral_rectangle_bounds :
    hpThetaJensenCubicNeg55RectangleLower 54 ≤
      (∫ u : ℝ in Set.Ioo (((54 : ℕ) : ℝ) / 80) ((((54 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ∧
    (∫ u : ℝ in Set.Ioo (((54 : ℕ) : ℝ) / 80) ((((54 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ≤
        hpThetaJensenCubicNeg55RectangleUpper 54 := by
  simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch054Neg55_integral_bounds

theorem hpThetaJensenCubicNeg55Batch055_integral_rectangle_bounds :
    hpThetaJensenCubicNeg55RectangleLower 55 ≤
      (∫ u : ℝ in Set.Ioo (((55 : ℕ) : ℝ) / 80) ((((55 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ∧
    (∫ u : ℝ in Set.Ioo (((55 : ℕ) : ℝ) / 80) ((((55 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ≤
        hpThetaJensenCubicNeg55RectangleUpper 55 := by
  simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch055Neg55_integral_bounds

theorem hpThetaJensenCubicNeg55Batch056_integral_rectangle_bounds :
    hpThetaJensenCubicNeg55RectangleLower 56 ≤
      (∫ u : ℝ in Set.Ioo (((56 : ℕ) : ℝ) / 80) ((((56 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ∧
    (∫ u : ℝ in Set.Ioo (((56 : ℕ) : ℝ) / 80) ((((56 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ≤
        hpThetaJensenCubicNeg55RectangleUpper 56 := by
  simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch056Neg55_integral_bounds

theorem hpThetaJensenCubicNeg55Batch057_integral_rectangle_bounds :
    hpThetaJensenCubicNeg55RectangleLower 57 ≤
      (∫ u : ℝ in Set.Ioo (((57 : ℕ) : ℝ) / 80) ((((57 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ∧
    (∫ u : ℝ in Set.Ioo (((57 : ℕ) : ℝ) / 80) ((((57 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ≤
        hpThetaJensenCubicNeg55RectangleUpper 57 := by
  simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch057Neg55_integral_bounds

theorem hpThetaJensenCubicNeg55Batch058_integral_rectangle_bounds :
    hpThetaJensenCubicNeg55RectangleLower 58 ≤
      (∫ u : ℝ in Set.Ioo (((58 : ℕ) : ℝ) / 80) ((((58 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ∧
    (∫ u : ℝ in Set.Ioo (((58 : ℕ) : ℝ) / 80) ((((58 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ≤
        hpThetaJensenCubicNeg55RectangleUpper 58 := by
  simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch058Neg55_integral_bounds

theorem hpThetaJensenCubicNeg55Batch059_integral_rectangle_bounds :
    hpThetaJensenCubicNeg55RectangleLower 59 ≤
      (∫ u : ℝ in Set.Ioo (((59 : ℕ) : ℝ) / 80) ((((59 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ∧
    (∫ u : ℝ in Set.Ioo (((59 : ℕ) : ℝ) / 80) ((((59 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ≤
        hpThetaJensenCubicNeg55RectangleUpper 59 := by
  simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch059Neg55_integral_bounds

theorem hpThetaJensenCubicNeg55Batch060_integral_rectangle_bounds :
    hpThetaJensenCubicNeg55RectangleLower 60 ≤
      (∫ u : ℝ in Set.Ioo (((60 : ℕ) : ℝ) / 80) ((((60 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ∧
    (∫ u : ℝ in Set.Ioo (((60 : ℕ) : ℝ) / 80) ((((60 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ≤
        hpThetaJensenCubicNeg55RectangleUpper 60 := by
  simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch060Neg55_integral_bounds

theorem hpThetaJensenCubicNeg55Batch061_integral_rectangle_bounds :
    hpThetaJensenCubicNeg55RectangleLower 61 ≤
      (∫ u : ℝ in Set.Ioo (((61 : ℕ) : ℝ) / 80) ((((61 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ∧
    (∫ u : ℝ in Set.Ioo (((61 : ℕ) : ℝ) / 80) ((((61 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ≤
        hpThetaJensenCubicNeg55RectangleUpper 61 := by
  simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch061Neg55_integral_bounds

theorem hpThetaJensenCubicNeg55Batch062_integral_rectangle_bounds :
    hpThetaJensenCubicNeg55RectangleLower 62 ≤
      (∫ u : ℝ in Set.Ioo (((62 : ℕ) : ℝ) / 80) ((((62 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ∧
    (∫ u : ℝ in Set.Ioo (((62 : ℕ) : ℝ) / 80) ((((62 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ≤
        hpThetaJensenCubicNeg55RectangleUpper 62 := by
  simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch062Neg55_integral_bounds

theorem hpThetaJensenCubicNeg55Batch063_integral_rectangle_bounds :
    hpThetaJensenCubicNeg55RectangleLower 63 ≤
      (∫ u : ℝ in Set.Ioo (((63 : ℕ) : ℝ) / 80) ((((63 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ∧
    (∫ u : ℝ in Set.Ioo (((63 : ℕ) : ℝ) / 80) ((((63 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ≤
        hpThetaJensenCubicNeg55RectangleUpper 63 := by
  simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch063Neg55_integral_bounds

theorem hpThetaJensenCubicNeg55Batch064_integral_rectangle_bounds :
    hpThetaJensenCubicNeg55RectangleLower 64 ≤
      (∫ u : ℝ in Set.Ioo (((64 : ℕ) : ℝ) / 80) ((((64 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ∧
    (∫ u : ℝ in Set.Ioo (((64 : ℕ) : ℝ) / 80) ((((64 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ≤
        hpThetaJensenCubicNeg55RectangleUpper 64 := by
  simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch064Neg55_integral_bounds

theorem hpThetaJensenCubicNeg55Batch065_integral_rectangle_bounds :
    hpThetaJensenCubicNeg55RectangleLower 65 ≤
      (∫ u : ℝ in Set.Ioo (((65 : ℕ) : ℝ) / 80) ((((65 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ∧
    (∫ u : ℝ in Set.Ioo (((65 : ℕ) : ℝ) / 80) ((((65 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ≤
        hpThetaJensenCubicNeg55RectangleUpper 65 := by
  simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch065Neg55_integral_bounds

theorem hpThetaJensenCubicNeg55Batch066_integral_rectangle_bounds :
    hpThetaJensenCubicNeg55RectangleLower 66 ≤
      (∫ u : ℝ in Set.Ioo (((66 : ℕ) : ℝ) / 80) ((((66 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ∧
    (∫ u : ℝ in Set.Ioo (((66 : ℕ) : ℝ) / 80) ((((66 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ≤
        hpThetaJensenCubicNeg55RectangleUpper 66 := by
  simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch066Neg55_integral_bounds

theorem hpThetaJensenCubicNeg55Batch067_integral_rectangle_bounds :
    hpThetaJensenCubicNeg55RectangleLower 67 ≤
      (∫ u : ℝ in Set.Ioo (((67 : ℕ) : ℝ) / 80) ((((67 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ∧
    (∫ u : ℝ in Set.Ioo (((67 : ℕ) : ℝ) / 80) ((((67 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ≤
        hpThetaJensenCubicNeg55RectangleUpper 67 := by
  simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch067Neg55_integral_bounds

theorem hpThetaJensenCubicNeg55Batch068_integral_rectangle_bounds :
    hpThetaJensenCubicNeg55RectangleLower 68 ≤
      (∫ u : ℝ in Set.Ioo (((68 : ℕ) : ℝ) / 80) ((((68 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ∧
    (∫ u : ℝ in Set.Ioo (((68 : ℕ) : ℝ) / 80) ((((68 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ≤
        hpThetaJensenCubicNeg55RectangleUpper 68 := by
  simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch068Neg55_integral_bounds

theorem hpThetaJensenCubicNeg55Batch069_integral_rectangle_bounds :
    hpThetaJensenCubicNeg55RectangleLower 69 ≤
      (∫ u : ℝ in Set.Ioo (((69 : ℕ) : ℝ) / 80) ((((69 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ∧
    (∫ u : ℝ in Set.Ioo (((69 : ℕ) : ℝ) / 80) ((((69 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ≤
        hpThetaJensenCubicNeg55RectangleUpper 69 := by
  simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch069Neg55_integral_bounds

theorem hpThetaJensenCubicNeg55Batch070_integral_rectangle_bounds :
    hpThetaJensenCubicNeg55RectangleLower 70 ≤
      (∫ u : ℝ in Set.Ioo (((70 : ℕ) : ℝ) / 80) ((((70 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ∧
    (∫ u : ℝ in Set.Ioo (((70 : ℕ) : ℝ) / 80) ((((70 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ≤
        hpThetaJensenCubicNeg55RectangleUpper 70 := by
  simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch070Neg55_integral_bounds

theorem hpThetaJensenCubicNeg55Batch071_integral_rectangle_bounds :
    hpThetaJensenCubicNeg55RectangleLower 71 ≤
      (∫ u : ℝ in Set.Ioo (((71 : ℕ) : ℝ) / 80) ((((71 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ∧
    (∫ u : ℝ in Set.Ioo (((71 : ℕ) : ℝ) / 80) ((((71 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ≤
        hpThetaJensenCubicNeg55RectangleUpper 71 := by
  simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch071Neg55_integral_bounds

theorem hpThetaJensenCubicNeg55Batch072_integral_rectangle_bounds :
    hpThetaJensenCubicNeg55RectangleLower 72 ≤
      (∫ u : ℝ in Set.Ioo (((72 : ℕ) : ℝ) / 80) ((((72 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ∧
    (∫ u : ℝ in Set.Ioo (((72 : ℕ) : ℝ) / 80) ((((72 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ≤
        hpThetaJensenCubicNeg55RectangleUpper 72 := by
  simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch072Neg55_integral_bounds

theorem hpThetaJensenCubicNeg55Batch073_integral_rectangle_bounds :
    hpThetaJensenCubicNeg55RectangleLower 73 ≤
      (∫ u : ℝ in Set.Ioo (((73 : ℕ) : ℝ) / 80) ((((73 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ∧
    (∫ u : ℝ in Set.Ioo (((73 : ℕ) : ℝ) / 80) ((((73 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ≤
        hpThetaJensenCubicNeg55RectangleUpper 73 := by
  simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch073Neg55_integral_bounds

theorem hpThetaJensenCubicNeg55Batch074_integral_rectangle_bounds :
    hpThetaJensenCubicNeg55RectangleLower 74 ≤
      (∫ u : ℝ in Set.Ioo (((74 : ℕ) : ℝ) / 80) ((((74 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ∧
    (∫ u : ℝ in Set.Ioo (((74 : ℕ) : ℝ) / 80) ((((74 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ≤
        hpThetaJensenCubicNeg55RectangleUpper 74 := by
  simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch074Neg55_integral_bounds

theorem hpThetaJensenCubicNeg55Batch075_integral_rectangle_bounds :
    hpThetaJensenCubicNeg55RectangleLower 75 ≤
      (∫ u : ℝ in Set.Ioo (((75 : ℕ) : ℝ) / 80) ((((75 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ∧
    (∫ u : ℝ in Set.Ioo (((75 : ℕ) : ℝ) / 80) ((((75 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ≤
        hpThetaJensenCubicNeg55RectangleUpper 75 := by
  simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch075Neg55_integral_bounds

theorem hpThetaJensenCubicNeg55Batch076_integral_rectangle_bounds :
    hpThetaJensenCubicNeg55RectangleLower 76 ≤
      (∫ u : ℝ in Set.Ioo (((76 : ℕ) : ℝ) / 80) ((((76 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ∧
    (∫ u : ℝ in Set.Ioo (((76 : ℕ) : ℝ) / 80) ((((76 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ≤
        hpThetaJensenCubicNeg55RectangleUpper 76 := by
  simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch076Neg55_integral_bounds

theorem hpThetaJensenCubicNeg55Batch077_integral_rectangle_bounds :
    hpThetaJensenCubicNeg55RectangleLower 77 ≤
      (∫ u : ℝ in Set.Ioo (((77 : ℕ) : ℝ) / 80) ((((77 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ∧
    (∫ u : ℝ in Set.Ioo (((77 : ℕ) : ℝ) / 80) ((((77 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ≤
        hpThetaJensenCubicNeg55RectangleUpper 77 := by
  simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch077Neg55_integral_bounds

theorem hpThetaJensenCubicNeg55Batch078_integral_rectangle_bounds :
    hpThetaJensenCubicNeg55RectangleLower 78 ≤
      (∫ u : ℝ in Set.Ioo (((78 : ℕ) : ℝ) / 80) ((((78 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ∧
    (∫ u : ℝ in Set.Ioo (((78 : ℕ) : ℝ) / 80) ((((78 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ≤
        hpThetaJensenCubicNeg55RectangleUpper 78 := by
  simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch078Neg55_integral_bounds

theorem hpThetaJensenCubicNeg55Batch079_integral_rectangle_bounds :
    hpThetaJensenCubicNeg55RectangleLower 79 ≤
      (∫ u : ℝ in Set.Ioo (((79 : ℕ) : ℝ) / 80) ((((79 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ∧
    (∫ u : ℝ in Set.Ioo (((79 : ℕ) : ℝ) / 80) ((((79 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ≤
        hpThetaJensenCubicNeg55RectangleUpper 79 := by
  simpa only [hpThetaJensenCubicNeg55RectangleLower, hpThetaJensenCubicNeg55RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch079Neg55_integral_bounds

theorem hpThetaJensenCubicNeg55_batchIntegral_rectangle_bounds (b : Fin 80) :
    hpThetaJensenCubicNeg55RectangleLower b.val ≤
      (∫ u : ℝ in Set.Ioo ((b.val : ℝ) / 80) (((b.val : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ∧
    (∫ u : ℝ in Set.Ioo ((b.val : ℝ) / 80) (((b.val : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-55) u) ≤
        hpThetaJensenCubicNeg55RectangleUpper b.val := by
  fin_cases b
  · exact hpThetaJensenCubicNeg55Batch000_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg55Batch001_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg55Batch002_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg55Batch003_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg55Batch004_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg55Batch005_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg55Batch006_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg55Batch007_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg55Batch008_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg55Batch009_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg55Batch010_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg55Batch011_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg55Batch012_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg55Batch013_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg55Batch014_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg55Batch015_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg55Batch016_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg55Batch017_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg55Batch018_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg55Batch019_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg55Batch020_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg55Batch021_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg55Batch022_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg55Batch023_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg55Batch024_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg55Batch025_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg55Batch026_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg55Batch027_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg55Batch028_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg55Batch029_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg55Batch030_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg55Batch031_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg55Batch032_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg55Batch033_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg55Batch034_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg55Batch035_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg55Batch036_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg55Batch037_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg55Batch038_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg55Batch039_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg55Batch040_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg55Batch041_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg55Batch042_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg55Batch043_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg55Batch044_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg55Batch045_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg55Batch046_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg55Batch047_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg55Batch048_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg55Batch049_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg55Batch050_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg55Batch051_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg55Batch052_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg55Batch053_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg55Batch054_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg55Batch055_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg55Batch056_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg55Batch057_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg55Batch058_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg55Batch059_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg55Batch060_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg55Batch061_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg55Batch062_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg55Batch063_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg55Batch064_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg55Batch065_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg55Batch066_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg55Batch067_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg55Batch068_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg55Batch069_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg55Batch070_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg55Batch071_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg55Batch072_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg55Batch073_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg55Batch074_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg55Batch075_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg55Batch076_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg55Batch077_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg55Batch078_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg55Batch079_integral_rectangle_bounds

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
