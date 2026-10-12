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


theorem hpThetaJensenCubicNeg42Batch000_integral_rectangle_bounds :
    hpThetaJensenCubicNeg42RectangleLower 0 ≤
      (∫ u : ℝ in Set.Ioo (((0 : ℕ) : ℝ) / 80) ((((0 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ∧
    (∫ u : ℝ in Set.Ioo (((0 : ℕ) : ℝ) / 80) ((((0 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ≤
        hpThetaJensenCubicNeg42RectangleUpper 0 := by
  simpa only [hpThetaJensenCubicNeg42RectangleLower, hpThetaJensenCubicNeg42RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch000Neg42_integral_bounds

theorem hpThetaJensenCubicNeg42Batch001_integral_rectangle_bounds :
    hpThetaJensenCubicNeg42RectangleLower 1 ≤
      (∫ u : ℝ in Set.Ioo (((1 : ℕ) : ℝ) / 80) ((((1 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ∧
    (∫ u : ℝ in Set.Ioo (((1 : ℕ) : ℝ) / 80) ((((1 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ≤
        hpThetaJensenCubicNeg42RectangleUpper 1 := by
  simpa only [hpThetaJensenCubicNeg42RectangleLower, hpThetaJensenCubicNeg42RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch001Neg42_integral_bounds

theorem hpThetaJensenCubicNeg42Batch002_integral_rectangle_bounds :
    hpThetaJensenCubicNeg42RectangleLower 2 ≤
      (∫ u : ℝ in Set.Ioo (((2 : ℕ) : ℝ) / 80) ((((2 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ∧
    (∫ u : ℝ in Set.Ioo (((2 : ℕ) : ℝ) / 80) ((((2 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ≤
        hpThetaJensenCubicNeg42RectangleUpper 2 := by
  simpa only [hpThetaJensenCubicNeg42RectangleLower, hpThetaJensenCubicNeg42RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch002Neg42_integral_bounds

theorem hpThetaJensenCubicNeg42Batch003_integral_rectangle_bounds :
    hpThetaJensenCubicNeg42RectangleLower 3 ≤
      (∫ u : ℝ in Set.Ioo (((3 : ℕ) : ℝ) / 80) ((((3 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ∧
    (∫ u : ℝ in Set.Ioo (((3 : ℕ) : ℝ) / 80) ((((3 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ≤
        hpThetaJensenCubicNeg42RectangleUpper 3 := by
  simpa only [hpThetaJensenCubicNeg42RectangleLower, hpThetaJensenCubicNeg42RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch003Neg42_integral_bounds

theorem hpThetaJensenCubicNeg42Batch004_integral_rectangle_bounds :
    hpThetaJensenCubicNeg42RectangleLower 4 ≤
      (∫ u : ℝ in Set.Ioo (((4 : ℕ) : ℝ) / 80) ((((4 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ∧
    (∫ u : ℝ in Set.Ioo (((4 : ℕ) : ℝ) / 80) ((((4 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ≤
        hpThetaJensenCubicNeg42RectangleUpper 4 := by
  simpa only [hpThetaJensenCubicNeg42RectangleLower, hpThetaJensenCubicNeg42RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch004Neg42_integral_bounds

theorem hpThetaJensenCubicNeg42Batch005_integral_rectangle_bounds :
    hpThetaJensenCubicNeg42RectangleLower 5 ≤
      (∫ u : ℝ in Set.Ioo (((5 : ℕ) : ℝ) / 80) ((((5 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ∧
    (∫ u : ℝ in Set.Ioo (((5 : ℕ) : ℝ) / 80) ((((5 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ≤
        hpThetaJensenCubicNeg42RectangleUpper 5 := by
  simpa only [hpThetaJensenCubicNeg42RectangleLower, hpThetaJensenCubicNeg42RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch005Neg42_integral_bounds

theorem hpThetaJensenCubicNeg42Batch006_integral_rectangle_bounds :
    hpThetaJensenCubicNeg42RectangleLower 6 ≤
      (∫ u : ℝ in Set.Ioo (((6 : ℕ) : ℝ) / 80) ((((6 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ∧
    (∫ u : ℝ in Set.Ioo (((6 : ℕ) : ℝ) / 80) ((((6 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ≤
        hpThetaJensenCubicNeg42RectangleUpper 6 := by
  simpa only [hpThetaJensenCubicNeg42RectangleLower, hpThetaJensenCubicNeg42RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch006Neg42_integral_bounds

theorem hpThetaJensenCubicNeg42Batch007_integral_rectangle_bounds :
    hpThetaJensenCubicNeg42RectangleLower 7 ≤
      (∫ u : ℝ in Set.Ioo (((7 : ℕ) : ℝ) / 80) ((((7 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ∧
    (∫ u : ℝ in Set.Ioo (((7 : ℕ) : ℝ) / 80) ((((7 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ≤
        hpThetaJensenCubicNeg42RectangleUpper 7 := by
  simpa only [hpThetaJensenCubicNeg42RectangleLower, hpThetaJensenCubicNeg42RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch007Neg42_integral_bounds

theorem hpThetaJensenCubicNeg42Batch008_integral_rectangle_bounds :
    hpThetaJensenCubicNeg42RectangleLower 8 ≤
      (∫ u : ℝ in Set.Ioo (((8 : ℕ) : ℝ) / 80) ((((8 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ∧
    (∫ u : ℝ in Set.Ioo (((8 : ℕ) : ℝ) / 80) ((((8 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ≤
        hpThetaJensenCubicNeg42RectangleUpper 8 := by
  simpa only [hpThetaJensenCubicNeg42RectangleLower, hpThetaJensenCubicNeg42RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch008Neg42_integral_bounds

theorem hpThetaJensenCubicNeg42Batch009_integral_rectangle_bounds :
    hpThetaJensenCubicNeg42RectangleLower 9 ≤
      (∫ u : ℝ in Set.Ioo (((9 : ℕ) : ℝ) / 80) ((((9 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ∧
    (∫ u : ℝ in Set.Ioo (((9 : ℕ) : ℝ) / 80) ((((9 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ≤
        hpThetaJensenCubicNeg42RectangleUpper 9 := by
  simpa only [hpThetaJensenCubicNeg42RectangleLower, hpThetaJensenCubicNeg42RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch009Neg42_integral_bounds

theorem hpThetaJensenCubicNeg42Batch010_integral_rectangle_bounds :
    hpThetaJensenCubicNeg42RectangleLower 10 ≤
      (∫ u : ℝ in Set.Ioo (((10 : ℕ) : ℝ) / 80) ((((10 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ∧
    (∫ u : ℝ in Set.Ioo (((10 : ℕ) : ℝ) / 80) ((((10 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ≤
        hpThetaJensenCubicNeg42RectangleUpper 10 := by
  simpa only [hpThetaJensenCubicNeg42RectangleLower, hpThetaJensenCubicNeg42RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch010Neg42_integral_bounds

theorem hpThetaJensenCubicNeg42Batch011_integral_rectangle_bounds :
    hpThetaJensenCubicNeg42RectangleLower 11 ≤
      (∫ u : ℝ in Set.Ioo (((11 : ℕ) : ℝ) / 80) ((((11 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ∧
    (∫ u : ℝ in Set.Ioo (((11 : ℕ) : ℝ) / 80) ((((11 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ≤
        hpThetaJensenCubicNeg42RectangleUpper 11 := by
  simpa only [hpThetaJensenCubicNeg42RectangleLower, hpThetaJensenCubicNeg42RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch011Neg42_integral_bounds

theorem hpThetaJensenCubicNeg42Batch012_integral_rectangle_bounds :
    hpThetaJensenCubicNeg42RectangleLower 12 ≤
      (∫ u : ℝ in Set.Ioo (((12 : ℕ) : ℝ) / 80) ((((12 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ∧
    (∫ u : ℝ in Set.Ioo (((12 : ℕ) : ℝ) / 80) ((((12 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ≤
        hpThetaJensenCubicNeg42RectangleUpper 12 := by
  simpa only [hpThetaJensenCubicNeg42RectangleLower, hpThetaJensenCubicNeg42RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch012Neg42_integral_bounds

theorem hpThetaJensenCubicNeg42Batch013_integral_rectangle_bounds :
    hpThetaJensenCubicNeg42RectangleLower 13 ≤
      (∫ u : ℝ in Set.Ioo (((13 : ℕ) : ℝ) / 80) ((((13 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ∧
    (∫ u : ℝ in Set.Ioo (((13 : ℕ) : ℝ) / 80) ((((13 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ≤
        hpThetaJensenCubicNeg42RectangleUpper 13 := by
  simpa only [hpThetaJensenCubicNeg42RectangleLower, hpThetaJensenCubicNeg42RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch013Neg42_integral_bounds

theorem hpThetaJensenCubicNeg42Batch014_integral_rectangle_bounds :
    hpThetaJensenCubicNeg42RectangleLower 14 ≤
      (∫ u : ℝ in Set.Ioo (((14 : ℕ) : ℝ) / 80) ((((14 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ∧
    (∫ u : ℝ in Set.Ioo (((14 : ℕ) : ℝ) / 80) ((((14 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ≤
        hpThetaJensenCubicNeg42RectangleUpper 14 := by
  simpa only [hpThetaJensenCubicNeg42RectangleLower, hpThetaJensenCubicNeg42RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch014Neg42_integral_bounds

theorem hpThetaJensenCubicNeg42Batch015_integral_rectangle_bounds :
    hpThetaJensenCubicNeg42RectangleLower 15 ≤
      (∫ u : ℝ in Set.Ioo (((15 : ℕ) : ℝ) / 80) ((((15 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ∧
    (∫ u : ℝ in Set.Ioo (((15 : ℕ) : ℝ) / 80) ((((15 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ≤
        hpThetaJensenCubicNeg42RectangleUpper 15 := by
  simpa only [hpThetaJensenCubicNeg42RectangleLower, hpThetaJensenCubicNeg42RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch015Neg42_integral_bounds

theorem hpThetaJensenCubicNeg42Batch016_integral_rectangle_bounds :
    hpThetaJensenCubicNeg42RectangleLower 16 ≤
      (∫ u : ℝ in Set.Ioo (((16 : ℕ) : ℝ) / 80) ((((16 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ∧
    (∫ u : ℝ in Set.Ioo (((16 : ℕ) : ℝ) / 80) ((((16 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ≤
        hpThetaJensenCubicNeg42RectangleUpper 16 := by
  simpa only [hpThetaJensenCubicNeg42RectangleLower, hpThetaJensenCubicNeg42RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch016Neg42_integral_bounds

theorem hpThetaJensenCubicNeg42Batch017_integral_rectangle_bounds :
    hpThetaJensenCubicNeg42RectangleLower 17 ≤
      (∫ u : ℝ in Set.Ioo (((17 : ℕ) : ℝ) / 80) ((((17 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ∧
    (∫ u : ℝ in Set.Ioo (((17 : ℕ) : ℝ) / 80) ((((17 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ≤
        hpThetaJensenCubicNeg42RectangleUpper 17 := by
  simpa only [hpThetaJensenCubicNeg42RectangleLower, hpThetaJensenCubicNeg42RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch017Neg42_integral_bounds

theorem hpThetaJensenCubicNeg42Batch018_integral_rectangle_bounds :
    hpThetaJensenCubicNeg42RectangleLower 18 ≤
      (∫ u : ℝ in Set.Ioo (((18 : ℕ) : ℝ) / 80) ((((18 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ∧
    (∫ u : ℝ in Set.Ioo (((18 : ℕ) : ℝ) / 80) ((((18 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ≤
        hpThetaJensenCubicNeg42RectangleUpper 18 := by
  simpa only [hpThetaJensenCubicNeg42RectangleLower, hpThetaJensenCubicNeg42RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch018Neg42_integral_bounds

theorem hpThetaJensenCubicNeg42Batch019_integral_rectangle_bounds :
    hpThetaJensenCubicNeg42RectangleLower 19 ≤
      (∫ u : ℝ in Set.Ioo (((19 : ℕ) : ℝ) / 80) ((((19 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ∧
    (∫ u : ℝ in Set.Ioo (((19 : ℕ) : ℝ) / 80) ((((19 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ≤
        hpThetaJensenCubicNeg42RectangleUpper 19 := by
  simpa only [hpThetaJensenCubicNeg42RectangleLower, hpThetaJensenCubicNeg42RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch019Neg42_integral_bounds

theorem hpThetaJensenCubicNeg42Batch020_integral_rectangle_bounds :
    hpThetaJensenCubicNeg42RectangleLower 20 ≤
      (∫ u : ℝ in Set.Ioo (((20 : ℕ) : ℝ) / 80) ((((20 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ∧
    (∫ u : ℝ in Set.Ioo (((20 : ℕ) : ℝ) / 80) ((((20 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ≤
        hpThetaJensenCubicNeg42RectangleUpper 20 := by
  simpa only [hpThetaJensenCubicNeg42RectangleLower, hpThetaJensenCubicNeg42RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch020Neg42_integral_bounds

theorem hpThetaJensenCubicNeg42Batch021_integral_rectangle_bounds :
    hpThetaJensenCubicNeg42RectangleLower 21 ≤
      (∫ u : ℝ in Set.Ioo (((21 : ℕ) : ℝ) / 80) ((((21 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ∧
    (∫ u : ℝ in Set.Ioo (((21 : ℕ) : ℝ) / 80) ((((21 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ≤
        hpThetaJensenCubicNeg42RectangleUpper 21 := by
  simpa only [hpThetaJensenCubicNeg42RectangleLower, hpThetaJensenCubicNeg42RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch021Neg42_integral_bounds

theorem hpThetaJensenCubicNeg42Batch022_integral_rectangle_bounds :
    hpThetaJensenCubicNeg42RectangleLower 22 ≤
      (∫ u : ℝ in Set.Ioo (((22 : ℕ) : ℝ) / 80) ((((22 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ∧
    (∫ u : ℝ in Set.Ioo (((22 : ℕ) : ℝ) / 80) ((((22 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ≤
        hpThetaJensenCubicNeg42RectangleUpper 22 := by
  simpa only [hpThetaJensenCubicNeg42RectangleLower, hpThetaJensenCubicNeg42RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch022Neg42_integral_bounds

theorem hpThetaJensenCubicNeg42Batch023_integral_rectangle_bounds :
    hpThetaJensenCubicNeg42RectangleLower 23 ≤
      (∫ u : ℝ in Set.Ioo (((23 : ℕ) : ℝ) / 80) ((((23 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ∧
    (∫ u : ℝ in Set.Ioo (((23 : ℕ) : ℝ) / 80) ((((23 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ≤
        hpThetaJensenCubicNeg42RectangleUpper 23 := by
  simpa only [hpThetaJensenCubicNeg42RectangleLower, hpThetaJensenCubicNeg42RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch023Neg42_integral_bounds

theorem hpThetaJensenCubicNeg42Batch024_integral_rectangle_bounds :
    hpThetaJensenCubicNeg42RectangleLower 24 ≤
      (∫ u : ℝ in Set.Ioo (((24 : ℕ) : ℝ) / 80) ((((24 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ∧
    (∫ u : ℝ in Set.Ioo (((24 : ℕ) : ℝ) / 80) ((((24 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ≤
        hpThetaJensenCubicNeg42RectangleUpper 24 := by
  simpa only [hpThetaJensenCubicNeg42RectangleLower, hpThetaJensenCubicNeg42RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch024Neg42_integral_bounds

theorem hpThetaJensenCubicNeg42Batch025_integral_rectangle_bounds :
    hpThetaJensenCubicNeg42RectangleLower 25 ≤
      (∫ u : ℝ in Set.Ioo (((25 : ℕ) : ℝ) / 80) ((((25 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ∧
    (∫ u : ℝ in Set.Ioo (((25 : ℕ) : ℝ) / 80) ((((25 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ≤
        hpThetaJensenCubicNeg42RectangleUpper 25 := by
  simpa only [hpThetaJensenCubicNeg42RectangleLower, hpThetaJensenCubicNeg42RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch025Neg42_integral_bounds

theorem hpThetaJensenCubicNeg42Batch026_integral_rectangle_bounds :
    hpThetaJensenCubicNeg42RectangleLower 26 ≤
      (∫ u : ℝ in Set.Ioo (((26 : ℕ) : ℝ) / 80) ((((26 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ∧
    (∫ u : ℝ in Set.Ioo (((26 : ℕ) : ℝ) / 80) ((((26 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ≤
        hpThetaJensenCubicNeg42RectangleUpper 26 := by
  simpa only [hpThetaJensenCubicNeg42RectangleLower, hpThetaJensenCubicNeg42RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch026Neg42_integral_bounds

theorem hpThetaJensenCubicNeg42Batch027_integral_rectangle_bounds :
    hpThetaJensenCubicNeg42RectangleLower 27 ≤
      (∫ u : ℝ in Set.Ioo (((27 : ℕ) : ℝ) / 80) ((((27 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ∧
    (∫ u : ℝ in Set.Ioo (((27 : ℕ) : ℝ) / 80) ((((27 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ≤
        hpThetaJensenCubicNeg42RectangleUpper 27 := by
  simpa only [hpThetaJensenCubicNeg42RectangleLower, hpThetaJensenCubicNeg42RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch027Neg42_integral_bounds

theorem hpThetaJensenCubicNeg42Batch028_integral_rectangle_bounds :
    hpThetaJensenCubicNeg42RectangleLower 28 ≤
      (∫ u : ℝ in Set.Ioo (((28 : ℕ) : ℝ) / 80) ((((28 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ∧
    (∫ u : ℝ in Set.Ioo (((28 : ℕ) : ℝ) / 80) ((((28 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ≤
        hpThetaJensenCubicNeg42RectangleUpper 28 := by
  simpa only [hpThetaJensenCubicNeg42RectangleLower, hpThetaJensenCubicNeg42RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch028Neg42_integral_bounds

theorem hpThetaJensenCubicNeg42Batch029_integral_rectangle_bounds :
    hpThetaJensenCubicNeg42RectangleLower 29 ≤
      (∫ u : ℝ in Set.Ioo (((29 : ℕ) : ℝ) / 80) ((((29 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ∧
    (∫ u : ℝ in Set.Ioo (((29 : ℕ) : ℝ) / 80) ((((29 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ≤
        hpThetaJensenCubicNeg42RectangleUpper 29 := by
  simpa only [hpThetaJensenCubicNeg42RectangleLower, hpThetaJensenCubicNeg42RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch029Neg42_integral_bounds

theorem hpThetaJensenCubicNeg42Batch030_integral_rectangle_bounds :
    hpThetaJensenCubicNeg42RectangleLower 30 ≤
      (∫ u : ℝ in Set.Ioo (((30 : ℕ) : ℝ) / 80) ((((30 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ∧
    (∫ u : ℝ in Set.Ioo (((30 : ℕ) : ℝ) / 80) ((((30 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ≤
        hpThetaJensenCubicNeg42RectangleUpper 30 := by
  simpa only [hpThetaJensenCubicNeg42RectangleLower, hpThetaJensenCubicNeg42RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch030Neg42_integral_bounds

theorem hpThetaJensenCubicNeg42Batch031_integral_rectangle_bounds :
    hpThetaJensenCubicNeg42RectangleLower 31 ≤
      (∫ u : ℝ in Set.Ioo (((31 : ℕ) : ℝ) / 80) ((((31 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ∧
    (∫ u : ℝ in Set.Ioo (((31 : ℕ) : ℝ) / 80) ((((31 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ≤
        hpThetaJensenCubicNeg42RectangleUpper 31 := by
  simpa only [hpThetaJensenCubicNeg42RectangleLower, hpThetaJensenCubicNeg42RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch031Neg42_integral_bounds

theorem hpThetaJensenCubicNeg42Batch032_integral_rectangle_bounds :
    hpThetaJensenCubicNeg42RectangleLower 32 ≤
      (∫ u : ℝ in Set.Ioo (((32 : ℕ) : ℝ) / 80) ((((32 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ∧
    (∫ u : ℝ in Set.Ioo (((32 : ℕ) : ℝ) / 80) ((((32 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ≤
        hpThetaJensenCubicNeg42RectangleUpper 32 := by
  simpa only [hpThetaJensenCubicNeg42RectangleLower, hpThetaJensenCubicNeg42RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch032Neg42_integral_bounds

theorem hpThetaJensenCubicNeg42Batch033_integral_rectangle_bounds :
    hpThetaJensenCubicNeg42RectangleLower 33 ≤
      (∫ u : ℝ in Set.Ioo (((33 : ℕ) : ℝ) / 80) ((((33 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ∧
    (∫ u : ℝ in Set.Ioo (((33 : ℕ) : ℝ) / 80) ((((33 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ≤
        hpThetaJensenCubicNeg42RectangleUpper 33 := by
  simpa only [hpThetaJensenCubicNeg42RectangleLower, hpThetaJensenCubicNeg42RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch033Neg42_integral_bounds

theorem hpThetaJensenCubicNeg42Batch034_integral_rectangle_bounds :
    hpThetaJensenCubicNeg42RectangleLower 34 ≤
      (∫ u : ℝ in Set.Ioo (((34 : ℕ) : ℝ) / 80) ((((34 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ∧
    (∫ u : ℝ in Set.Ioo (((34 : ℕ) : ℝ) / 80) ((((34 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ≤
        hpThetaJensenCubicNeg42RectangleUpper 34 := by
  simpa only [hpThetaJensenCubicNeg42RectangleLower, hpThetaJensenCubicNeg42RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch034Neg42_integral_bounds

theorem hpThetaJensenCubicNeg42Batch035_integral_rectangle_bounds :
    hpThetaJensenCubicNeg42RectangleLower 35 ≤
      (∫ u : ℝ in Set.Ioo (((35 : ℕ) : ℝ) / 80) ((((35 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ∧
    (∫ u : ℝ in Set.Ioo (((35 : ℕ) : ℝ) / 80) ((((35 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ≤
        hpThetaJensenCubicNeg42RectangleUpper 35 := by
  simpa only [hpThetaJensenCubicNeg42RectangleLower, hpThetaJensenCubicNeg42RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch035Neg42_integral_bounds

theorem hpThetaJensenCubicNeg42Batch036_integral_rectangle_bounds :
    hpThetaJensenCubicNeg42RectangleLower 36 ≤
      (∫ u : ℝ in Set.Ioo (((36 : ℕ) : ℝ) / 80) ((((36 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ∧
    (∫ u : ℝ in Set.Ioo (((36 : ℕ) : ℝ) / 80) ((((36 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ≤
        hpThetaJensenCubicNeg42RectangleUpper 36 := by
  simpa only [hpThetaJensenCubicNeg42RectangleLower, hpThetaJensenCubicNeg42RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch036Neg42_integral_bounds

theorem hpThetaJensenCubicNeg42Batch037_integral_rectangle_bounds :
    hpThetaJensenCubicNeg42RectangleLower 37 ≤
      (∫ u : ℝ in Set.Ioo (((37 : ℕ) : ℝ) / 80) ((((37 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ∧
    (∫ u : ℝ in Set.Ioo (((37 : ℕ) : ℝ) / 80) ((((37 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ≤
        hpThetaJensenCubicNeg42RectangleUpper 37 := by
  simpa only [hpThetaJensenCubicNeg42RectangleLower, hpThetaJensenCubicNeg42RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch037Neg42_integral_bounds

theorem hpThetaJensenCubicNeg42Batch038_integral_rectangle_bounds :
    hpThetaJensenCubicNeg42RectangleLower 38 ≤
      (∫ u : ℝ in Set.Ioo (((38 : ℕ) : ℝ) / 80) ((((38 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ∧
    (∫ u : ℝ in Set.Ioo (((38 : ℕ) : ℝ) / 80) ((((38 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ≤
        hpThetaJensenCubicNeg42RectangleUpper 38 := by
  simpa only [hpThetaJensenCubicNeg42RectangleLower, hpThetaJensenCubicNeg42RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch038Neg42_integral_bounds

theorem hpThetaJensenCubicNeg42Batch039_integral_rectangle_bounds :
    hpThetaJensenCubicNeg42RectangleLower 39 ≤
      (∫ u : ℝ in Set.Ioo (((39 : ℕ) : ℝ) / 80) ((((39 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ∧
    (∫ u : ℝ in Set.Ioo (((39 : ℕ) : ℝ) / 80) ((((39 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ≤
        hpThetaJensenCubicNeg42RectangleUpper 39 := by
  simpa only [hpThetaJensenCubicNeg42RectangleLower, hpThetaJensenCubicNeg42RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch039Neg42_integral_bounds

theorem hpThetaJensenCubicNeg42Batch040_integral_rectangle_bounds :
    hpThetaJensenCubicNeg42RectangleLower 40 ≤
      (∫ u : ℝ in Set.Ioo (((40 : ℕ) : ℝ) / 80) ((((40 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ∧
    (∫ u : ℝ in Set.Ioo (((40 : ℕ) : ℝ) / 80) ((((40 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ≤
        hpThetaJensenCubicNeg42RectangleUpper 40 := by
  simpa only [hpThetaJensenCubicNeg42RectangleLower, hpThetaJensenCubicNeg42RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch040Neg42_integral_bounds

theorem hpThetaJensenCubicNeg42Batch041_integral_rectangle_bounds :
    hpThetaJensenCubicNeg42RectangleLower 41 ≤
      (∫ u : ℝ in Set.Ioo (((41 : ℕ) : ℝ) / 80) ((((41 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ∧
    (∫ u : ℝ in Set.Ioo (((41 : ℕ) : ℝ) / 80) ((((41 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ≤
        hpThetaJensenCubicNeg42RectangleUpper 41 := by
  simpa only [hpThetaJensenCubicNeg42RectangleLower, hpThetaJensenCubicNeg42RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch041Neg42_integral_bounds

theorem hpThetaJensenCubicNeg42Batch042_integral_rectangle_bounds :
    hpThetaJensenCubicNeg42RectangleLower 42 ≤
      (∫ u : ℝ in Set.Ioo (((42 : ℕ) : ℝ) / 80) ((((42 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ∧
    (∫ u : ℝ in Set.Ioo (((42 : ℕ) : ℝ) / 80) ((((42 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ≤
        hpThetaJensenCubicNeg42RectangleUpper 42 := by
  simpa only [hpThetaJensenCubicNeg42RectangleLower, hpThetaJensenCubicNeg42RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch042Neg42_integral_bounds

theorem hpThetaJensenCubicNeg42Batch043_integral_rectangle_bounds :
    hpThetaJensenCubicNeg42RectangleLower 43 ≤
      (∫ u : ℝ in Set.Ioo (((43 : ℕ) : ℝ) / 80) ((((43 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ∧
    (∫ u : ℝ in Set.Ioo (((43 : ℕ) : ℝ) / 80) ((((43 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ≤
        hpThetaJensenCubicNeg42RectangleUpper 43 := by
  simpa only [hpThetaJensenCubicNeg42RectangleLower, hpThetaJensenCubicNeg42RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch043Neg42_integral_bounds

theorem hpThetaJensenCubicNeg42Batch044_integral_rectangle_bounds :
    hpThetaJensenCubicNeg42RectangleLower 44 ≤
      (∫ u : ℝ in Set.Ioo (((44 : ℕ) : ℝ) / 80) ((((44 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ∧
    (∫ u : ℝ in Set.Ioo (((44 : ℕ) : ℝ) / 80) ((((44 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ≤
        hpThetaJensenCubicNeg42RectangleUpper 44 := by
  simpa only [hpThetaJensenCubicNeg42RectangleLower, hpThetaJensenCubicNeg42RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch044Neg42_integral_bounds

theorem hpThetaJensenCubicNeg42Batch045_integral_rectangle_bounds :
    hpThetaJensenCubicNeg42RectangleLower 45 ≤
      (∫ u : ℝ in Set.Ioo (((45 : ℕ) : ℝ) / 80) ((((45 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ∧
    (∫ u : ℝ in Set.Ioo (((45 : ℕ) : ℝ) / 80) ((((45 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ≤
        hpThetaJensenCubicNeg42RectangleUpper 45 := by
  simpa only [hpThetaJensenCubicNeg42RectangleLower, hpThetaJensenCubicNeg42RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch045Neg42_integral_bounds

theorem hpThetaJensenCubicNeg42Batch046_integral_rectangle_bounds :
    hpThetaJensenCubicNeg42RectangleLower 46 ≤
      (∫ u : ℝ in Set.Ioo (((46 : ℕ) : ℝ) / 80) ((((46 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ∧
    (∫ u : ℝ in Set.Ioo (((46 : ℕ) : ℝ) / 80) ((((46 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ≤
        hpThetaJensenCubicNeg42RectangleUpper 46 := by
  simpa only [hpThetaJensenCubicNeg42RectangleLower, hpThetaJensenCubicNeg42RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch046Neg42_integral_bounds

theorem hpThetaJensenCubicNeg42Batch047_integral_rectangle_bounds :
    hpThetaJensenCubicNeg42RectangleLower 47 ≤
      (∫ u : ℝ in Set.Ioo (((47 : ℕ) : ℝ) / 80) ((((47 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ∧
    (∫ u : ℝ in Set.Ioo (((47 : ℕ) : ℝ) / 80) ((((47 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ≤
        hpThetaJensenCubicNeg42RectangleUpper 47 := by
  simpa only [hpThetaJensenCubicNeg42RectangleLower, hpThetaJensenCubicNeg42RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch047Neg42_integral_bounds

theorem hpThetaJensenCubicNeg42Batch048_integral_rectangle_bounds :
    hpThetaJensenCubicNeg42RectangleLower 48 ≤
      (∫ u : ℝ in Set.Ioo (((48 : ℕ) : ℝ) / 80) ((((48 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ∧
    (∫ u : ℝ in Set.Ioo (((48 : ℕ) : ℝ) / 80) ((((48 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ≤
        hpThetaJensenCubicNeg42RectangleUpper 48 := by
  simpa only [hpThetaJensenCubicNeg42RectangleLower, hpThetaJensenCubicNeg42RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch048Neg42_integral_bounds

theorem hpThetaJensenCubicNeg42Batch049_integral_rectangle_bounds :
    hpThetaJensenCubicNeg42RectangleLower 49 ≤
      (∫ u : ℝ in Set.Ioo (((49 : ℕ) : ℝ) / 80) ((((49 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ∧
    (∫ u : ℝ in Set.Ioo (((49 : ℕ) : ℝ) / 80) ((((49 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ≤
        hpThetaJensenCubicNeg42RectangleUpper 49 := by
  simpa only [hpThetaJensenCubicNeg42RectangleLower, hpThetaJensenCubicNeg42RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch049Neg42_integral_bounds

theorem hpThetaJensenCubicNeg42Batch050_integral_rectangle_bounds :
    hpThetaJensenCubicNeg42RectangleLower 50 ≤
      (∫ u : ℝ in Set.Ioo (((50 : ℕ) : ℝ) / 80) ((((50 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ∧
    (∫ u : ℝ in Set.Ioo (((50 : ℕ) : ℝ) / 80) ((((50 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ≤
        hpThetaJensenCubicNeg42RectangleUpper 50 := by
  simpa only [hpThetaJensenCubicNeg42RectangleLower, hpThetaJensenCubicNeg42RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch050Neg42_integral_bounds

theorem hpThetaJensenCubicNeg42Batch051_integral_rectangle_bounds :
    hpThetaJensenCubicNeg42RectangleLower 51 ≤
      (∫ u : ℝ in Set.Ioo (((51 : ℕ) : ℝ) / 80) ((((51 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ∧
    (∫ u : ℝ in Set.Ioo (((51 : ℕ) : ℝ) / 80) ((((51 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ≤
        hpThetaJensenCubicNeg42RectangleUpper 51 := by
  simpa only [hpThetaJensenCubicNeg42RectangleLower, hpThetaJensenCubicNeg42RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch051Neg42_integral_bounds

theorem hpThetaJensenCubicNeg42Batch052_integral_rectangle_bounds :
    hpThetaJensenCubicNeg42RectangleLower 52 ≤
      (∫ u : ℝ in Set.Ioo (((52 : ℕ) : ℝ) / 80) ((((52 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ∧
    (∫ u : ℝ in Set.Ioo (((52 : ℕ) : ℝ) / 80) ((((52 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ≤
        hpThetaJensenCubicNeg42RectangleUpper 52 := by
  simpa only [hpThetaJensenCubicNeg42RectangleLower, hpThetaJensenCubicNeg42RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch052Neg42_integral_bounds

theorem hpThetaJensenCubicNeg42Batch053_integral_rectangle_bounds :
    hpThetaJensenCubicNeg42RectangleLower 53 ≤
      (∫ u : ℝ in Set.Ioo (((53 : ℕ) : ℝ) / 80) ((((53 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ∧
    (∫ u : ℝ in Set.Ioo (((53 : ℕ) : ℝ) / 80) ((((53 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ≤
        hpThetaJensenCubicNeg42RectangleUpper 53 := by
  simpa only [hpThetaJensenCubicNeg42RectangleLower, hpThetaJensenCubicNeg42RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch053Neg42_integral_bounds

theorem hpThetaJensenCubicNeg42Batch054_integral_rectangle_bounds :
    hpThetaJensenCubicNeg42RectangleLower 54 ≤
      (∫ u : ℝ in Set.Ioo (((54 : ℕ) : ℝ) / 80) ((((54 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ∧
    (∫ u : ℝ in Set.Ioo (((54 : ℕ) : ℝ) / 80) ((((54 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ≤
        hpThetaJensenCubicNeg42RectangleUpper 54 := by
  simpa only [hpThetaJensenCubicNeg42RectangleLower, hpThetaJensenCubicNeg42RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch054Neg42_integral_bounds

theorem hpThetaJensenCubicNeg42Batch055_integral_rectangle_bounds :
    hpThetaJensenCubicNeg42RectangleLower 55 ≤
      (∫ u : ℝ in Set.Ioo (((55 : ℕ) : ℝ) / 80) ((((55 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ∧
    (∫ u : ℝ in Set.Ioo (((55 : ℕ) : ℝ) / 80) ((((55 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ≤
        hpThetaJensenCubicNeg42RectangleUpper 55 := by
  simpa only [hpThetaJensenCubicNeg42RectangleLower, hpThetaJensenCubicNeg42RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch055Neg42_integral_bounds

theorem hpThetaJensenCubicNeg42Batch056_integral_rectangle_bounds :
    hpThetaJensenCubicNeg42RectangleLower 56 ≤
      (∫ u : ℝ in Set.Ioo (((56 : ℕ) : ℝ) / 80) ((((56 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ∧
    (∫ u : ℝ in Set.Ioo (((56 : ℕ) : ℝ) / 80) ((((56 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ≤
        hpThetaJensenCubicNeg42RectangleUpper 56 := by
  simpa only [hpThetaJensenCubicNeg42RectangleLower, hpThetaJensenCubicNeg42RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch056Neg42_integral_bounds

theorem hpThetaJensenCubicNeg42Batch057_integral_rectangle_bounds :
    hpThetaJensenCubicNeg42RectangleLower 57 ≤
      (∫ u : ℝ in Set.Ioo (((57 : ℕ) : ℝ) / 80) ((((57 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ∧
    (∫ u : ℝ in Set.Ioo (((57 : ℕ) : ℝ) / 80) ((((57 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ≤
        hpThetaJensenCubicNeg42RectangleUpper 57 := by
  simpa only [hpThetaJensenCubicNeg42RectangleLower, hpThetaJensenCubicNeg42RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch057Neg42_integral_bounds

theorem hpThetaJensenCubicNeg42Batch058_integral_rectangle_bounds :
    hpThetaJensenCubicNeg42RectangleLower 58 ≤
      (∫ u : ℝ in Set.Ioo (((58 : ℕ) : ℝ) / 80) ((((58 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ∧
    (∫ u : ℝ in Set.Ioo (((58 : ℕ) : ℝ) / 80) ((((58 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ≤
        hpThetaJensenCubicNeg42RectangleUpper 58 := by
  simpa only [hpThetaJensenCubicNeg42RectangleLower, hpThetaJensenCubicNeg42RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch058Neg42_integral_bounds

theorem hpThetaJensenCubicNeg42Batch059_integral_rectangle_bounds :
    hpThetaJensenCubicNeg42RectangleLower 59 ≤
      (∫ u : ℝ in Set.Ioo (((59 : ℕ) : ℝ) / 80) ((((59 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ∧
    (∫ u : ℝ in Set.Ioo (((59 : ℕ) : ℝ) / 80) ((((59 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ≤
        hpThetaJensenCubicNeg42RectangleUpper 59 := by
  simpa only [hpThetaJensenCubicNeg42RectangleLower, hpThetaJensenCubicNeg42RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch059Neg42_integral_bounds

theorem hpThetaJensenCubicNeg42Batch060_integral_rectangle_bounds :
    hpThetaJensenCubicNeg42RectangleLower 60 ≤
      (∫ u : ℝ in Set.Ioo (((60 : ℕ) : ℝ) / 80) ((((60 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ∧
    (∫ u : ℝ in Set.Ioo (((60 : ℕ) : ℝ) / 80) ((((60 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ≤
        hpThetaJensenCubicNeg42RectangleUpper 60 := by
  simpa only [hpThetaJensenCubicNeg42RectangleLower, hpThetaJensenCubicNeg42RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch060Neg42_integral_bounds

theorem hpThetaJensenCubicNeg42Batch061_integral_rectangle_bounds :
    hpThetaJensenCubicNeg42RectangleLower 61 ≤
      (∫ u : ℝ in Set.Ioo (((61 : ℕ) : ℝ) / 80) ((((61 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ∧
    (∫ u : ℝ in Set.Ioo (((61 : ℕ) : ℝ) / 80) ((((61 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ≤
        hpThetaJensenCubicNeg42RectangleUpper 61 := by
  simpa only [hpThetaJensenCubicNeg42RectangleLower, hpThetaJensenCubicNeg42RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch061Neg42_integral_bounds

theorem hpThetaJensenCubicNeg42Batch062_integral_rectangle_bounds :
    hpThetaJensenCubicNeg42RectangleLower 62 ≤
      (∫ u : ℝ in Set.Ioo (((62 : ℕ) : ℝ) / 80) ((((62 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ∧
    (∫ u : ℝ in Set.Ioo (((62 : ℕ) : ℝ) / 80) ((((62 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ≤
        hpThetaJensenCubicNeg42RectangleUpper 62 := by
  simpa only [hpThetaJensenCubicNeg42RectangleLower, hpThetaJensenCubicNeg42RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch062Neg42_integral_bounds

theorem hpThetaJensenCubicNeg42Batch063_integral_rectangle_bounds :
    hpThetaJensenCubicNeg42RectangleLower 63 ≤
      (∫ u : ℝ in Set.Ioo (((63 : ℕ) : ℝ) / 80) ((((63 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ∧
    (∫ u : ℝ in Set.Ioo (((63 : ℕ) : ℝ) / 80) ((((63 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ≤
        hpThetaJensenCubicNeg42RectangleUpper 63 := by
  simpa only [hpThetaJensenCubicNeg42RectangleLower, hpThetaJensenCubicNeg42RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch063Neg42_integral_bounds

theorem hpThetaJensenCubicNeg42Batch064_integral_rectangle_bounds :
    hpThetaJensenCubicNeg42RectangleLower 64 ≤
      (∫ u : ℝ in Set.Ioo (((64 : ℕ) : ℝ) / 80) ((((64 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ∧
    (∫ u : ℝ in Set.Ioo (((64 : ℕ) : ℝ) / 80) ((((64 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ≤
        hpThetaJensenCubicNeg42RectangleUpper 64 := by
  simpa only [hpThetaJensenCubicNeg42RectangleLower, hpThetaJensenCubicNeg42RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch064Neg42_integral_bounds

theorem hpThetaJensenCubicNeg42Batch065_integral_rectangle_bounds :
    hpThetaJensenCubicNeg42RectangleLower 65 ≤
      (∫ u : ℝ in Set.Ioo (((65 : ℕ) : ℝ) / 80) ((((65 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ∧
    (∫ u : ℝ in Set.Ioo (((65 : ℕ) : ℝ) / 80) ((((65 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ≤
        hpThetaJensenCubicNeg42RectangleUpper 65 := by
  simpa only [hpThetaJensenCubicNeg42RectangleLower, hpThetaJensenCubicNeg42RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch065Neg42_integral_bounds

theorem hpThetaJensenCubicNeg42Batch066_integral_rectangle_bounds :
    hpThetaJensenCubicNeg42RectangleLower 66 ≤
      (∫ u : ℝ in Set.Ioo (((66 : ℕ) : ℝ) / 80) ((((66 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ∧
    (∫ u : ℝ in Set.Ioo (((66 : ℕ) : ℝ) / 80) ((((66 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ≤
        hpThetaJensenCubicNeg42RectangleUpper 66 := by
  simpa only [hpThetaJensenCubicNeg42RectangleLower, hpThetaJensenCubicNeg42RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch066Neg42_integral_bounds

theorem hpThetaJensenCubicNeg42Batch067_integral_rectangle_bounds :
    hpThetaJensenCubicNeg42RectangleLower 67 ≤
      (∫ u : ℝ in Set.Ioo (((67 : ℕ) : ℝ) / 80) ((((67 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ∧
    (∫ u : ℝ in Set.Ioo (((67 : ℕ) : ℝ) / 80) ((((67 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ≤
        hpThetaJensenCubicNeg42RectangleUpper 67 := by
  simpa only [hpThetaJensenCubicNeg42RectangleLower, hpThetaJensenCubicNeg42RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch067Neg42_integral_bounds

theorem hpThetaJensenCubicNeg42Batch068_integral_rectangle_bounds :
    hpThetaJensenCubicNeg42RectangleLower 68 ≤
      (∫ u : ℝ in Set.Ioo (((68 : ℕ) : ℝ) / 80) ((((68 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ∧
    (∫ u : ℝ in Set.Ioo (((68 : ℕ) : ℝ) / 80) ((((68 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ≤
        hpThetaJensenCubicNeg42RectangleUpper 68 := by
  simpa only [hpThetaJensenCubicNeg42RectangleLower, hpThetaJensenCubicNeg42RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch068Neg42_integral_bounds

theorem hpThetaJensenCubicNeg42Batch069_integral_rectangle_bounds :
    hpThetaJensenCubicNeg42RectangleLower 69 ≤
      (∫ u : ℝ in Set.Ioo (((69 : ℕ) : ℝ) / 80) ((((69 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ∧
    (∫ u : ℝ in Set.Ioo (((69 : ℕ) : ℝ) / 80) ((((69 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ≤
        hpThetaJensenCubicNeg42RectangleUpper 69 := by
  simpa only [hpThetaJensenCubicNeg42RectangleLower, hpThetaJensenCubicNeg42RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch069Neg42_integral_bounds

theorem hpThetaJensenCubicNeg42Batch070_integral_rectangle_bounds :
    hpThetaJensenCubicNeg42RectangleLower 70 ≤
      (∫ u : ℝ in Set.Ioo (((70 : ℕ) : ℝ) / 80) ((((70 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ∧
    (∫ u : ℝ in Set.Ioo (((70 : ℕ) : ℝ) / 80) ((((70 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ≤
        hpThetaJensenCubicNeg42RectangleUpper 70 := by
  simpa only [hpThetaJensenCubicNeg42RectangleLower, hpThetaJensenCubicNeg42RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch070Neg42_integral_bounds

theorem hpThetaJensenCubicNeg42Batch071_integral_rectangle_bounds :
    hpThetaJensenCubicNeg42RectangleLower 71 ≤
      (∫ u : ℝ in Set.Ioo (((71 : ℕ) : ℝ) / 80) ((((71 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ∧
    (∫ u : ℝ in Set.Ioo (((71 : ℕ) : ℝ) / 80) ((((71 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ≤
        hpThetaJensenCubicNeg42RectangleUpper 71 := by
  simpa only [hpThetaJensenCubicNeg42RectangleLower, hpThetaJensenCubicNeg42RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch071Neg42_integral_bounds

theorem hpThetaJensenCubicNeg42Batch072_integral_rectangle_bounds :
    hpThetaJensenCubicNeg42RectangleLower 72 ≤
      (∫ u : ℝ in Set.Ioo (((72 : ℕ) : ℝ) / 80) ((((72 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ∧
    (∫ u : ℝ in Set.Ioo (((72 : ℕ) : ℝ) / 80) ((((72 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ≤
        hpThetaJensenCubicNeg42RectangleUpper 72 := by
  simpa only [hpThetaJensenCubicNeg42RectangleLower, hpThetaJensenCubicNeg42RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch072Neg42_integral_bounds

theorem hpThetaJensenCubicNeg42Batch073_integral_rectangle_bounds :
    hpThetaJensenCubicNeg42RectangleLower 73 ≤
      (∫ u : ℝ in Set.Ioo (((73 : ℕ) : ℝ) / 80) ((((73 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ∧
    (∫ u : ℝ in Set.Ioo (((73 : ℕ) : ℝ) / 80) ((((73 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ≤
        hpThetaJensenCubicNeg42RectangleUpper 73 := by
  simpa only [hpThetaJensenCubicNeg42RectangleLower, hpThetaJensenCubicNeg42RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch073Neg42_integral_bounds

theorem hpThetaJensenCubicNeg42Batch074_integral_rectangle_bounds :
    hpThetaJensenCubicNeg42RectangleLower 74 ≤
      (∫ u : ℝ in Set.Ioo (((74 : ℕ) : ℝ) / 80) ((((74 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ∧
    (∫ u : ℝ in Set.Ioo (((74 : ℕ) : ℝ) / 80) ((((74 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ≤
        hpThetaJensenCubicNeg42RectangleUpper 74 := by
  simpa only [hpThetaJensenCubicNeg42RectangleLower, hpThetaJensenCubicNeg42RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch074Neg42_integral_bounds

theorem hpThetaJensenCubicNeg42Batch075_integral_rectangle_bounds :
    hpThetaJensenCubicNeg42RectangleLower 75 ≤
      (∫ u : ℝ in Set.Ioo (((75 : ℕ) : ℝ) / 80) ((((75 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ∧
    (∫ u : ℝ in Set.Ioo (((75 : ℕ) : ℝ) / 80) ((((75 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ≤
        hpThetaJensenCubicNeg42RectangleUpper 75 := by
  simpa only [hpThetaJensenCubicNeg42RectangleLower, hpThetaJensenCubicNeg42RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch075Neg42_integral_bounds

theorem hpThetaJensenCubicNeg42Batch076_integral_rectangle_bounds :
    hpThetaJensenCubicNeg42RectangleLower 76 ≤
      (∫ u : ℝ in Set.Ioo (((76 : ℕ) : ℝ) / 80) ((((76 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ∧
    (∫ u : ℝ in Set.Ioo (((76 : ℕ) : ℝ) / 80) ((((76 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ≤
        hpThetaJensenCubicNeg42RectangleUpper 76 := by
  simpa only [hpThetaJensenCubicNeg42RectangleLower, hpThetaJensenCubicNeg42RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch076Neg42_integral_bounds

theorem hpThetaJensenCubicNeg42Batch077_integral_rectangle_bounds :
    hpThetaJensenCubicNeg42RectangleLower 77 ≤
      (∫ u : ℝ in Set.Ioo (((77 : ℕ) : ℝ) / 80) ((((77 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ∧
    (∫ u : ℝ in Set.Ioo (((77 : ℕ) : ℝ) / 80) ((((77 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ≤
        hpThetaJensenCubicNeg42RectangleUpper 77 := by
  simpa only [hpThetaJensenCubicNeg42RectangleLower, hpThetaJensenCubicNeg42RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch077Neg42_integral_bounds

theorem hpThetaJensenCubicNeg42Batch078_integral_rectangle_bounds :
    hpThetaJensenCubicNeg42RectangleLower 78 ≤
      (∫ u : ℝ in Set.Ioo (((78 : ℕ) : ℝ) / 80) ((((78 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ∧
    (∫ u : ℝ in Set.Ioo (((78 : ℕ) : ℝ) / 80) ((((78 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ≤
        hpThetaJensenCubicNeg42RectangleUpper 78 := by
  simpa only [hpThetaJensenCubicNeg42RectangleLower, hpThetaJensenCubicNeg42RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch078Neg42_integral_bounds

theorem hpThetaJensenCubicNeg42Batch079_integral_rectangle_bounds :
    hpThetaJensenCubicNeg42RectangleLower 79 ≤
      (∫ u : ℝ in Set.Ioo (((79 : ℕ) : ℝ) / 80) ((((79 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ∧
    (∫ u : ℝ in Set.Ioo (((79 : ℕ) : ℝ) / 80) ((((79 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ≤
        hpThetaJensenCubicNeg42RectangleUpper 79 := by
  simpa only [hpThetaJensenCubicNeg42RectangleLower, hpThetaJensenCubicNeg42RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch079Neg42_integral_bounds

theorem hpThetaJensenCubicNeg42_batchIntegral_rectangle_bounds (b : Fin 80) :
    hpThetaJensenCubicNeg42RectangleLower b.val ≤
      (∫ u : ℝ in Set.Ioo ((b.val : ℝ) / 80) (((b.val : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ∧
    (∫ u : ℝ in Set.Ioo ((b.val : ℝ) / 80) (((b.val : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-42) u) ≤
        hpThetaJensenCubicNeg42RectangleUpper b.val := by
  fin_cases b
  · exact hpThetaJensenCubicNeg42Batch000_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg42Batch001_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg42Batch002_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg42Batch003_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg42Batch004_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg42Batch005_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg42Batch006_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg42Batch007_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg42Batch008_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg42Batch009_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg42Batch010_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg42Batch011_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg42Batch012_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg42Batch013_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg42Batch014_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg42Batch015_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg42Batch016_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg42Batch017_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg42Batch018_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg42Batch019_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg42Batch020_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg42Batch021_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg42Batch022_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg42Batch023_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg42Batch024_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg42Batch025_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg42Batch026_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg42Batch027_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg42Batch028_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg42Batch029_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg42Batch030_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg42Batch031_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg42Batch032_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg42Batch033_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg42Batch034_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg42Batch035_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg42Batch036_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg42Batch037_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg42Batch038_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg42Batch039_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg42Batch040_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg42Batch041_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg42Batch042_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg42Batch043_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg42Batch044_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg42Batch045_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg42Batch046_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg42Batch047_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg42Batch048_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg42Batch049_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg42Batch050_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg42Batch051_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg42Batch052_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg42Batch053_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg42Batch054_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg42Batch055_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg42Batch056_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg42Batch057_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg42Batch058_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg42Batch059_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg42Batch060_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg42Batch061_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg42Batch062_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg42Batch063_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg42Batch064_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg42Batch065_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg42Batch066_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg42Batch067_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg42Batch068_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg42Batch069_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg42Batch070_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg42Batch071_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg42Batch072_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg42Batch073_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg42Batch074_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg42Batch075_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg42Batch076_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg42Batch077_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg42Batch078_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg42Batch079_integral_rectangle_bounds

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
  constructor
  · convert le_trans hpThetaJensenCubicNeg42_rectangle_lower_numeric hl using 1 <;> norm_num
  · convert le_trans hu hpThetaJensenCubicNeg42_rectangle_upper_numeric using 1 <;> norm_num

#print axioms hpThetaJensenCubicNeg42_batchIntegral_rectangle_bounds
#print axioms hpThetaJensenCubicNeg42_batchIntegral_sum
#print axioms hpThetaJensenCubicNeg42_finiteIntegral_bounds
end HodgeProofHP
