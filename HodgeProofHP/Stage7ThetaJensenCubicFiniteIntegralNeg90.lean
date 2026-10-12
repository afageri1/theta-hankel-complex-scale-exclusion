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


theorem hpThetaJensenCubicNeg90Batch000_integral_rectangle_bounds :
    hpThetaJensenCubicNeg90RectangleLower 0 ≤
      (∫ u : ℝ in Set.Ioo (((0 : ℕ) : ℝ) / 80) ((((0 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ∧
    (∫ u : ℝ in Set.Ioo (((0 : ℕ) : ℝ) / 80) ((((0 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ≤
        hpThetaJensenCubicNeg90RectangleUpper 0 := by
  simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch000Neg90_integral_bounds

theorem hpThetaJensenCubicNeg90Batch001_integral_rectangle_bounds :
    hpThetaJensenCubicNeg90RectangleLower 1 ≤
      (∫ u : ℝ in Set.Ioo (((1 : ℕ) : ℝ) / 80) ((((1 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ∧
    (∫ u : ℝ in Set.Ioo (((1 : ℕ) : ℝ) / 80) ((((1 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ≤
        hpThetaJensenCubicNeg90RectangleUpper 1 := by
  simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch001Neg90_integral_bounds

theorem hpThetaJensenCubicNeg90Batch002_integral_rectangle_bounds :
    hpThetaJensenCubicNeg90RectangleLower 2 ≤
      (∫ u : ℝ in Set.Ioo (((2 : ℕ) : ℝ) / 80) ((((2 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ∧
    (∫ u : ℝ in Set.Ioo (((2 : ℕ) : ℝ) / 80) ((((2 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ≤
        hpThetaJensenCubicNeg90RectangleUpper 2 := by
  simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch002Neg90_integral_bounds

theorem hpThetaJensenCubicNeg90Batch003_integral_rectangle_bounds :
    hpThetaJensenCubicNeg90RectangleLower 3 ≤
      (∫ u : ℝ in Set.Ioo (((3 : ℕ) : ℝ) / 80) ((((3 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ∧
    (∫ u : ℝ in Set.Ioo (((3 : ℕ) : ℝ) / 80) ((((3 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ≤
        hpThetaJensenCubicNeg90RectangleUpper 3 := by
  simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch003Neg90_integral_bounds

theorem hpThetaJensenCubicNeg90Batch004_integral_rectangle_bounds :
    hpThetaJensenCubicNeg90RectangleLower 4 ≤
      (∫ u : ℝ in Set.Ioo (((4 : ℕ) : ℝ) / 80) ((((4 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ∧
    (∫ u : ℝ in Set.Ioo (((4 : ℕ) : ℝ) / 80) ((((4 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ≤
        hpThetaJensenCubicNeg90RectangleUpper 4 := by
  simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch004Neg90_integral_bounds

theorem hpThetaJensenCubicNeg90Batch005_integral_rectangle_bounds :
    hpThetaJensenCubicNeg90RectangleLower 5 ≤
      (∫ u : ℝ in Set.Ioo (((5 : ℕ) : ℝ) / 80) ((((5 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ∧
    (∫ u : ℝ in Set.Ioo (((5 : ℕ) : ℝ) / 80) ((((5 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ≤
        hpThetaJensenCubicNeg90RectangleUpper 5 := by
  simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch005Neg90_integral_bounds

theorem hpThetaJensenCubicNeg90Batch006_integral_rectangle_bounds :
    hpThetaJensenCubicNeg90RectangleLower 6 ≤
      (∫ u : ℝ in Set.Ioo (((6 : ℕ) : ℝ) / 80) ((((6 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ∧
    (∫ u : ℝ in Set.Ioo (((6 : ℕ) : ℝ) / 80) ((((6 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ≤
        hpThetaJensenCubicNeg90RectangleUpper 6 := by
  simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch006Neg90_integral_bounds

theorem hpThetaJensenCubicNeg90Batch007_integral_rectangle_bounds :
    hpThetaJensenCubicNeg90RectangleLower 7 ≤
      (∫ u : ℝ in Set.Ioo (((7 : ℕ) : ℝ) / 80) ((((7 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ∧
    (∫ u : ℝ in Set.Ioo (((7 : ℕ) : ℝ) / 80) ((((7 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ≤
        hpThetaJensenCubicNeg90RectangleUpper 7 := by
  simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch007Neg90_integral_bounds

theorem hpThetaJensenCubicNeg90Batch008_integral_rectangle_bounds :
    hpThetaJensenCubicNeg90RectangleLower 8 ≤
      (∫ u : ℝ in Set.Ioo (((8 : ℕ) : ℝ) / 80) ((((8 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ∧
    (∫ u : ℝ in Set.Ioo (((8 : ℕ) : ℝ) / 80) ((((8 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ≤
        hpThetaJensenCubicNeg90RectangleUpper 8 := by
  simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch008Neg90_integral_bounds

theorem hpThetaJensenCubicNeg90Batch009_integral_rectangle_bounds :
    hpThetaJensenCubicNeg90RectangleLower 9 ≤
      (∫ u : ℝ in Set.Ioo (((9 : ℕ) : ℝ) / 80) ((((9 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ∧
    (∫ u : ℝ in Set.Ioo (((9 : ℕ) : ℝ) / 80) ((((9 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ≤
        hpThetaJensenCubicNeg90RectangleUpper 9 := by
  simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch009Neg90_integral_bounds

theorem hpThetaJensenCubicNeg90Batch010_integral_rectangle_bounds :
    hpThetaJensenCubicNeg90RectangleLower 10 ≤
      (∫ u : ℝ in Set.Ioo (((10 : ℕ) : ℝ) / 80) ((((10 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ∧
    (∫ u : ℝ in Set.Ioo (((10 : ℕ) : ℝ) / 80) ((((10 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ≤
        hpThetaJensenCubicNeg90RectangleUpper 10 := by
  simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch010Neg90_integral_bounds

theorem hpThetaJensenCubicNeg90Batch011_integral_rectangle_bounds :
    hpThetaJensenCubicNeg90RectangleLower 11 ≤
      (∫ u : ℝ in Set.Ioo (((11 : ℕ) : ℝ) / 80) ((((11 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ∧
    (∫ u : ℝ in Set.Ioo (((11 : ℕ) : ℝ) / 80) ((((11 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ≤
        hpThetaJensenCubicNeg90RectangleUpper 11 := by
  simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch011Neg90_integral_bounds

theorem hpThetaJensenCubicNeg90Batch012_integral_rectangle_bounds :
    hpThetaJensenCubicNeg90RectangleLower 12 ≤
      (∫ u : ℝ in Set.Ioo (((12 : ℕ) : ℝ) / 80) ((((12 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ∧
    (∫ u : ℝ in Set.Ioo (((12 : ℕ) : ℝ) / 80) ((((12 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ≤
        hpThetaJensenCubicNeg90RectangleUpper 12 := by
  simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch012Neg90_integral_bounds

theorem hpThetaJensenCubicNeg90Batch013_integral_rectangle_bounds :
    hpThetaJensenCubicNeg90RectangleLower 13 ≤
      (∫ u : ℝ in Set.Ioo (((13 : ℕ) : ℝ) / 80) ((((13 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ∧
    (∫ u : ℝ in Set.Ioo (((13 : ℕ) : ℝ) / 80) ((((13 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ≤
        hpThetaJensenCubicNeg90RectangleUpper 13 := by
  simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch013Neg90_integral_bounds

theorem hpThetaJensenCubicNeg90Batch014_integral_rectangle_bounds :
    hpThetaJensenCubicNeg90RectangleLower 14 ≤
      (∫ u : ℝ in Set.Ioo (((14 : ℕ) : ℝ) / 80) ((((14 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ∧
    (∫ u : ℝ in Set.Ioo (((14 : ℕ) : ℝ) / 80) ((((14 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ≤
        hpThetaJensenCubicNeg90RectangleUpper 14 := by
  simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch014Neg90_integral_bounds

theorem hpThetaJensenCubicNeg90Batch015_integral_rectangle_bounds :
    hpThetaJensenCubicNeg90RectangleLower 15 ≤
      (∫ u : ℝ in Set.Ioo (((15 : ℕ) : ℝ) / 80) ((((15 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ∧
    (∫ u : ℝ in Set.Ioo (((15 : ℕ) : ℝ) / 80) ((((15 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ≤
        hpThetaJensenCubicNeg90RectangleUpper 15 := by
  simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch015Neg90_integral_bounds

theorem hpThetaJensenCubicNeg90Batch016_integral_rectangle_bounds :
    hpThetaJensenCubicNeg90RectangleLower 16 ≤
      (∫ u : ℝ in Set.Ioo (((16 : ℕ) : ℝ) / 80) ((((16 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ∧
    (∫ u : ℝ in Set.Ioo (((16 : ℕ) : ℝ) / 80) ((((16 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ≤
        hpThetaJensenCubicNeg90RectangleUpper 16 := by
  simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch016Neg90_integral_bounds

theorem hpThetaJensenCubicNeg90Batch017_integral_rectangle_bounds :
    hpThetaJensenCubicNeg90RectangleLower 17 ≤
      (∫ u : ℝ in Set.Ioo (((17 : ℕ) : ℝ) / 80) ((((17 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ∧
    (∫ u : ℝ in Set.Ioo (((17 : ℕ) : ℝ) / 80) ((((17 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ≤
        hpThetaJensenCubicNeg90RectangleUpper 17 := by
  simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch017Neg90_integral_bounds

theorem hpThetaJensenCubicNeg90Batch018_integral_rectangle_bounds :
    hpThetaJensenCubicNeg90RectangleLower 18 ≤
      (∫ u : ℝ in Set.Ioo (((18 : ℕ) : ℝ) / 80) ((((18 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ∧
    (∫ u : ℝ in Set.Ioo (((18 : ℕ) : ℝ) / 80) ((((18 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ≤
        hpThetaJensenCubicNeg90RectangleUpper 18 := by
  simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch018Neg90_integral_bounds

theorem hpThetaJensenCubicNeg90Batch019_integral_rectangle_bounds :
    hpThetaJensenCubicNeg90RectangleLower 19 ≤
      (∫ u : ℝ in Set.Ioo (((19 : ℕ) : ℝ) / 80) ((((19 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ∧
    (∫ u : ℝ in Set.Ioo (((19 : ℕ) : ℝ) / 80) ((((19 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ≤
        hpThetaJensenCubicNeg90RectangleUpper 19 := by
  simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch019Neg90_integral_bounds

theorem hpThetaJensenCubicNeg90Batch020_integral_rectangle_bounds :
    hpThetaJensenCubicNeg90RectangleLower 20 ≤
      (∫ u : ℝ in Set.Ioo (((20 : ℕ) : ℝ) / 80) ((((20 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ∧
    (∫ u : ℝ in Set.Ioo (((20 : ℕ) : ℝ) / 80) ((((20 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ≤
        hpThetaJensenCubicNeg90RectangleUpper 20 := by
  simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch020Neg90_integral_bounds

theorem hpThetaJensenCubicNeg90Batch021_integral_rectangle_bounds :
    hpThetaJensenCubicNeg90RectangleLower 21 ≤
      (∫ u : ℝ in Set.Ioo (((21 : ℕ) : ℝ) / 80) ((((21 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ∧
    (∫ u : ℝ in Set.Ioo (((21 : ℕ) : ℝ) / 80) ((((21 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ≤
        hpThetaJensenCubicNeg90RectangleUpper 21 := by
  simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch021Neg90_integral_bounds

theorem hpThetaJensenCubicNeg90Batch022_integral_rectangle_bounds :
    hpThetaJensenCubicNeg90RectangleLower 22 ≤
      (∫ u : ℝ in Set.Ioo (((22 : ℕ) : ℝ) / 80) ((((22 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ∧
    (∫ u : ℝ in Set.Ioo (((22 : ℕ) : ℝ) / 80) ((((22 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ≤
        hpThetaJensenCubicNeg90RectangleUpper 22 := by
  simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch022Neg90_integral_bounds

theorem hpThetaJensenCubicNeg90Batch023_integral_rectangle_bounds :
    hpThetaJensenCubicNeg90RectangleLower 23 ≤
      (∫ u : ℝ in Set.Ioo (((23 : ℕ) : ℝ) / 80) ((((23 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ∧
    (∫ u : ℝ in Set.Ioo (((23 : ℕ) : ℝ) / 80) ((((23 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ≤
        hpThetaJensenCubicNeg90RectangleUpper 23 := by
  simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch023Neg90_integral_bounds

theorem hpThetaJensenCubicNeg90Batch024_integral_rectangle_bounds :
    hpThetaJensenCubicNeg90RectangleLower 24 ≤
      (∫ u : ℝ in Set.Ioo (((24 : ℕ) : ℝ) / 80) ((((24 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ∧
    (∫ u : ℝ in Set.Ioo (((24 : ℕ) : ℝ) / 80) ((((24 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ≤
        hpThetaJensenCubicNeg90RectangleUpper 24 := by
  simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch024Neg90_integral_bounds

theorem hpThetaJensenCubicNeg90Batch025_integral_rectangle_bounds :
    hpThetaJensenCubicNeg90RectangleLower 25 ≤
      (∫ u : ℝ in Set.Ioo (((25 : ℕ) : ℝ) / 80) ((((25 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ∧
    (∫ u : ℝ in Set.Ioo (((25 : ℕ) : ℝ) / 80) ((((25 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ≤
        hpThetaJensenCubicNeg90RectangleUpper 25 := by
  simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch025Neg90_integral_bounds

theorem hpThetaJensenCubicNeg90Batch026_integral_rectangle_bounds :
    hpThetaJensenCubicNeg90RectangleLower 26 ≤
      (∫ u : ℝ in Set.Ioo (((26 : ℕ) : ℝ) / 80) ((((26 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ∧
    (∫ u : ℝ in Set.Ioo (((26 : ℕ) : ℝ) / 80) ((((26 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ≤
        hpThetaJensenCubicNeg90RectangleUpper 26 := by
  simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch026Neg90_integral_bounds

theorem hpThetaJensenCubicNeg90Batch027_integral_rectangle_bounds :
    hpThetaJensenCubicNeg90RectangleLower 27 ≤
      (∫ u : ℝ in Set.Ioo (((27 : ℕ) : ℝ) / 80) ((((27 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ∧
    (∫ u : ℝ in Set.Ioo (((27 : ℕ) : ℝ) / 80) ((((27 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ≤
        hpThetaJensenCubicNeg90RectangleUpper 27 := by
  simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch027Neg90_integral_bounds

theorem hpThetaJensenCubicNeg90Batch028_integral_rectangle_bounds :
    hpThetaJensenCubicNeg90RectangleLower 28 ≤
      (∫ u : ℝ in Set.Ioo (((28 : ℕ) : ℝ) / 80) ((((28 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ∧
    (∫ u : ℝ in Set.Ioo (((28 : ℕ) : ℝ) / 80) ((((28 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ≤
        hpThetaJensenCubicNeg90RectangleUpper 28 := by
  simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch028Neg90_integral_bounds

theorem hpThetaJensenCubicNeg90Batch029_integral_rectangle_bounds :
    hpThetaJensenCubicNeg90RectangleLower 29 ≤
      (∫ u : ℝ in Set.Ioo (((29 : ℕ) : ℝ) / 80) ((((29 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ∧
    (∫ u : ℝ in Set.Ioo (((29 : ℕ) : ℝ) / 80) ((((29 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ≤
        hpThetaJensenCubicNeg90RectangleUpper 29 := by
  simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch029Neg90_integral_bounds

theorem hpThetaJensenCubicNeg90Batch030_integral_rectangle_bounds :
    hpThetaJensenCubicNeg90RectangleLower 30 ≤
      (∫ u : ℝ in Set.Ioo (((30 : ℕ) : ℝ) / 80) ((((30 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ∧
    (∫ u : ℝ in Set.Ioo (((30 : ℕ) : ℝ) / 80) ((((30 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ≤
        hpThetaJensenCubicNeg90RectangleUpper 30 := by
  simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch030Neg90_integral_bounds

theorem hpThetaJensenCubicNeg90Batch031_integral_rectangle_bounds :
    hpThetaJensenCubicNeg90RectangleLower 31 ≤
      (∫ u : ℝ in Set.Ioo (((31 : ℕ) : ℝ) / 80) ((((31 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ∧
    (∫ u : ℝ in Set.Ioo (((31 : ℕ) : ℝ) / 80) ((((31 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ≤
        hpThetaJensenCubicNeg90RectangleUpper 31 := by
  simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch031Neg90_integral_bounds

theorem hpThetaJensenCubicNeg90Batch032_integral_rectangle_bounds :
    hpThetaJensenCubicNeg90RectangleLower 32 ≤
      (∫ u : ℝ in Set.Ioo (((32 : ℕ) : ℝ) / 80) ((((32 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ∧
    (∫ u : ℝ in Set.Ioo (((32 : ℕ) : ℝ) / 80) ((((32 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ≤
        hpThetaJensenCubicNeg90RectangleUpper 32 := by
  simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch032Neg90_integral_bounds

theorem hpThetaJensenCubicNeg90Batch033_integral_rectangle_bounds :
    hpThetaJensenCubicNeg90RectangleLower 33 ≤
      (∫ u : ℝ in Set.Ioo (((33 : ℕ) : ℝ) / 80) ((((33 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ∧
    (∫ u : ℝ in Set.Ioo (((33 : ℕ) : ℝ) / 80) ((((33 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ≤
        hpThetaJensenCubicNeg90RectangleUpper 33 := by
  simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch033Neg90_integral_bounds

theorem hpThetaJensenCubicNeg90Batch034_integral_rectangle_bounds :
    hpThetaJensenCubicNeg90RectangleLower 34 ≤
      (∫ u : ℝ in Set.Ioo (((34 : ℕ) : ℝ) / 80) ((((34 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ∧
    (∫ u : ℝ in Set.Ioo (((34 : ℕ) : ℝ) / 80) ((((34 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ≤
        hpThetaJensenCubicNeg90RectangleUpper 34 := by
  simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch034Neg90_integral_bounds

theorem hpThetaJensenCubicNeg90Batch035_integral_rectangle_bounds :
    hpThetaJensenCubicNeg90RectangleLower 35 ≤
      (∫ u : ℝ in Set.Ioo (((35 : ℕ) : ℝ) / 80) ((((35 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ∧
    (∫ u : ℝ in Set.Ioo (((35 : ℕ) : ℝ) / 80) ((((35 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ≤
        hpThetaJensenCubicNeg90RectangleUpper 35 := by
  simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch035Neg90_integral_bounds

theorem hpThetaJensenCubicNeg90Batch036_integral_rectangle_bounds :
    hpThetaJensenCubicNeg90RectangleLower 36 ≤
      (∫ u : ℝ in Set.Ioo (((36 : ℕ) : ℝ) / 80) ((((36 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ∧
    (∫ u : ℝ in Set.Ioo (((36 : ℕ) : ℝ) / 80) ((((36 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ≤
        hpThetaJensenCubicNeg90RectangleUpper 36 := by
  simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch036Neg90_integral_bounds

theorem hpThetaJensenCubicNeg90Batch037_integral_rectangle_bounds :
    hpThetaJensenCubicNeg90RectangleLower 37 ≤
      (∫ u : ℝ in Set.Ioo (((37 : ℕ) : ℝ) / 80) ((((37 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ∧
    (∫ u : ℝ in Set.Ioo (((37 : ℕ) : ℝ) / 80) ((((37 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ≤
        hpThetaJensenCubicNeg90RectangleUpper 37 := by
  simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch037Neg90_integral_bounds

theorem hpThetaJensenCubicNeg90Batch038_integral_rectangle_bounds :
    hpThetaJensenCubicNeg90RectangleLower 38 ≤
      (∫ u : ℝ in Set.Ioo (((38 : ℕ) : ℝ) / 80) ((((38 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ∧
    (∫ u : ℝ in Set.Ioo (((38 : ℕ) : ℝ) / 80) ((((38 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ≤
        hpThetaJensenCubicNeg90RectangleUpper 38 := by
  simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch038Neg90_integral_bounds

theorem hpThetaJensenCubicNeg90Batch039_integral_rectangle_bounds :
    hpThetaJensenCubicNeg90RectangleLower 39 ≤
      (∫ u : ℝ in Set.Ioo (((39 : ℕ) : ℝ) / 80) ((((39 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ∧
    (∫ u : ℝ in Set.Ioo (((39 : ℕ) : ℝ) / 80) ((((39 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ≤
        hpThetaJensenCubicNeg90RectangleUpper 39 := by
  simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch039Neg90_integral_bounds

theorem hpThetaJensenCubicNeg90Batch040_integral_rectangle_bounds :
    hpThetaJensenCubicNeg90RectangleLower 40 ≤
      (∫ u : ℝ in Set.Ioo (((40 : ℕ) : ℝ) / 80) ((((40 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ∧
    (∫ u : ℝ in Set.Ioo (((40 : ℕ) : ℝ) / 80) ((((40 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ≤
        hpThetaJensenCubicNeg90RectangleUpper 40 := by
  simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch040Neg90_integral_bounds

theorem hpThetaJensenCubicNeg90Batch041_integral_rectangle_bounds :
    hpThetaJensenCubicNeg90RectangleLower 41 ≤
      (∫ u : ℝ in Set.Ioo (((41 : ℕ) : ℝ) / 80) ((((41 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ∧
    (∫ u : ℝ in Set.Ioo (((41 : ℕ) : ℝ) / 80) ((((41 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ≤
        hpThetaJensenCubicNeg90RectangleUpper 41 := by
  simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch041Neg90_integral_bounds

theorem hpThetaJensenCubicNeg90Batch042_integral_rectangle_bounds :
    hpThetaJensenCubicNeg90RectangleLower 42 ≤
      (∫ u : ℝ in Set.Ioo (((42 : ℕ) : ℝ) / 80) ((((42 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ∧
    (∫ u : ℝ in Set.Ioo (((42 : ℕ) : ℝ) / 80) ((((42 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ≤
        hpThetaJensenCubicNeg90RectangleUpper 42 := by
  simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch042Neg90_integral_bounds

theorem hpThetaJensenCubicNeg90Batch043_integral_rectangle_bounds :
    hpThetaJensenCubicNeg90RectangleLower 43 ≤
      (∫ u : ℝ in Set.Ioo (((43 : ℕ) : ℝ) / 80) ((((43 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ∧
    (∫ u : ℝ in Set.Ioo (((43 : ℕ) : ℝ) / 80) ((((43 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ≤
        hpThetaJensenCubicNeg90RectangleUpper 43 := by
  simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch043Neg90_integral_bounds

theorem hpThetaJensenCubicNeg90Batch044_integral_rectangle_bounds :
    hpThetaJensenCubicNeg90RectangleLower 44 ≤
      (∫ u : ℝ in Set.Ioo (((44 : ℕ) : ℝ) / 80) ((((44 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ∧
    (∫ u : ℝ in Set.Ioo (((44 : ℕ) : ℝ) / 80) ((((44 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ≤
        hpThetaJensenCubicNeg90RectangleUpper 44 := by
  simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch044Neg90_integral_bounds

theorem hpThetaJensenCubicNeg90Batch045_integral_rectangle_bounds :
    hpThetaJensenCubicNeg90RectangleLower 45 ≤
      (∫ u : ℝ in Set.Ioo (((45 : ℕ) : ℝ) / 80) ((((45 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ∧
    (∫ u : ℝ in Set.Ioo (((45 : ℕ) : ℝ) / 80) ((((45 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ≤
        hpThetaJensenCubicNeg90RectangleUpper 45 := by
  simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch045Neg90_integral_bounds

theorem hpThetaJensenCubicNeg90Batch046_integral_rectangle_bounds :
    hpThetaJensenCubicNeg90RectangleLower 46 ≤
      (∫ u : ℝ in Set.Ioo (((46 : ℕ) : ℝ) / 80) ((((46 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ∧
    (∫ u : ℝ in Set.Ioo (((46 : ℕ) : ℝ) / 80) ((((46 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ≤
        hpThetaJensenCubicNeg90RectangleUpper 46 := by
  simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch046Neg90_integral_bounds

theorem hpThetaJensenCubicNeg90Batch047_integral_rectangle_bounds :
    hpThetaJensenCubicNeg90RectangleLower 47 ≤
      (∫ u : ℝ in Set.Ioo (((47 : ℕ) : ℝ) / 80) ((((47 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ∧
    (∫ u : ℝ in Set.Ioo (((47 : ℕ) : ℝ) / 80) ((((47 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ≤
        hpThetaJensenCubicNeg90RectangleUpper 47 := by
  simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch047Neg90_integral_bounds

theorem hpThetaJensenCubicNeg90Batch048_integral_rectangle_bounds :
    hpThetaJensenCubicNeg90RectangleLower 48 ≤
      (∫ u : ℝ in Set.Ioo (((48 : ℕ) : ℝ) / 80) ((((48 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ∧
    (∫ u : ℝ in Set.Ioo (((48 : ℕ) : ℝ) / 80) ((((48 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ≤
        hpThetaJensenCubicNeg90RectangleUpper 48 := by
  simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch048Neg90_integral_bounds

theorem hpThetaJensenCubicNeg90Batch049_integral_rectangle_bounds :
    hpThetaJensenCubicNeg90RectangleLower 49 ≤
      (∫ u : ℝ in Set.Ioo (((49 : ℕ) : ℝ) / 80) ((((49 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ∧
    (∫ u : ℝ in Set.Ioo (((49 : ℕ) : ℝ) / 80) ((((49 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ≤
        hpThetaJensenCubicNeg90RectangleUpper 49 := by
  simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch049Neg90_integral_bounds

theorem hpThetaJensenCubicNeg90Batch050_integral_rectangle_bounds :
    hpThetaJensenCubicNeg90RectangleLower 50 ≤
      (∫ u : ℝ in Set.Ioo (((50 : ℕ) : ℝ) / 80) ((((50 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ∧
    (∫ u : ℝ in Set.Ioo (((50 : ℕ) : ℝ) / 80) ((((50 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ≤
        hpThetaJensenCubicNeg90RectangleUpper 50 := by
  simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch050Neg90_integral_bounds

theorem hpThetaJensenCubicNeg90Batch051_integral_rectangle_bounds :
    hpThetaJensenCubicNeg90RectangleLower 51 ≤
      (∫ u : ℝ in Set.Ioo (((51 : ℕ) : ℝ) / 80) ((((51 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ∧
    (∫ u : ℝ in Set.Ioo (((51 : ℕ) : ℝ) / 80) ((((51 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ≤
        hpThetaJensenCubicNeg90RectangleUpper 51 := by
  simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch051Neg90_integral_bounds

theorem hpThetaJensenCubicNeg90Batch052_integral_rectangle_bounds :
    hpThetaJensenCubicNeg90RectangleLower 52 ≤
      (∫ u : ℝ in Set.Ioo (((52 : ℕ) : ℝ) / 80) ((((52 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ∧
    (∫ u : ℝ in Set.Ioo (((52 : ℕ) : ℝ) / 80) ((((52 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ≤
        hpThetaJensenCubicNeg90RectangleUpper 52 := by
  simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch052Neg90_integral_bounds

theorem hpThetaJensenCubicNeg90Batch053_integral_rectangle_bounds :
    hpThetaJensenCubicNeg90RectangleLower 53 ≤
      (∫ u : ℝ in Set.Ioo (((53 : ℕ) : ℝ) / 80) ((((53 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ∧
    (∫ u : ℝ in Set.Ioo (((53 : ℕ) : ℝ) / 80) ((((53 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ≤
        hpThetaJensenCubicNeg90RectangleUpper 53 := by
  simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch053Neg90_integral_bounds

theorem hpThetaJensenCubicNeg90Batch054_integral_rectangle_bounds :
    hpThetaJensenCubicNeg90RectangleLower 54 ≤
      (∫ u : ℝ in Set.Ioo (((54 : ℕ) : ℝ) / 80) ((((54 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ∧
    (∫ u : ℝ in Set.Ioo (((54 : ℕ) : ℝ) / 80) ((((54 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ≤
        hpThetaJensenCubicNeg90RectangleUpper 54 := by
  simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch054Neg90_integral_bounds

theorem hpThetaJensenCubicNeg90Batch055_integral_rectangle_bounds :
    hpThetaJensenCubicNeg90RectangleLower 55 ≤
      (∫ u : ℝ in Set.Ioo (((55 : ℕ) : ℝ) / 80) ((((55 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ∧
    (∫ u : ℝ in Set.Ioo (((55 : ℕ) : ℝ) / 80) ((((55 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ≤
        hpThetaJensenCubicNeg90RectangleUpper 55 := by
  simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch055Neg90_integral_bounds

theorem hpThetaJensenCubicNeg90Batch056_integral_rectangle_bounds :
    hpThetaJensenCubicNeg90RectangleLower 56 ≤
      (∫ u : ℝ in Set.Ioo (((56 : ℕ) : ℝ) / 80) ((((56 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ∧
    (∫ u : ℝ in Set.Ioo (((56 : ℕ) : ℝ) / 80) ((((56 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ≤
        hpThetaJensenCubicNeg90RectangleUpper 56 := by
  simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch056Neg90_integral_bounds

theorem hpThetaJensenCubicNeg90Batch057_integral_rectangle_bounds :
    hpThetaJensenCubicNeg90RectangleLower 57 ≤
      (∫ u : ℝ in Set.Ioo (((57 : ℕ) : ℝ) / 80) ((((57 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ∧
    (∫ u : ℝ in Set.Ioo (((57 : ℕ) : ℝ) / 80) ((((57 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ≤
        hpThetaJensenCubicNeg90RectangleUpper 57 := by
  simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch057Neg90_integral_bounds

theorem hpThetaJensenCubicNeg90Batch058_integral_rectangle_bounds :
    hpThetaJensenCubicNeg90RectangleLower 58 ≤
      (∫ u : ℝ in Set.Ioo (((58 : ℕ) : ℝ) / 80) ((((58 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ∧
    (∫ u : ℝ in Set.Ioo (((58 : ℕ) : ℝ) / 80) ((((58 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ≤
        hpThetaJensenCubicNeg90RectangleUpper 58 := by
  simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch058Neg90_integral_bounds

theorem hpThetaJensenCubicNeg90Batch059_integral_rectangle_bounds :
    hpThetaJensenCubicNeg90RectangleLower 59 ≤
      (∫ u : ℝ in Set.Ioo (((59 : ℕ) : ℝ) / 80) ((((59 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ∧
    (∫ u : ℝ in Set.Ioo (((59 : ℕ) : ℝ) / 80) ((((59 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ≤
        hpThetaJensenCubicNeg90RectangleUpper 59 := by
  simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch059Neg90_integral_bounds

theorem hpThetaJensenCubicNeg90Batch060_integral_rectangle_bounds :
    hpThetaJensenCubicNeg90RectangleLower 60 ≤
      (∫ u : ℝ in Set.Ioo (((60 : ℕ) : ℝ) / 80) ((((60 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ∧
    (∫ u : ℝ in Set.Ioo (((60 : ℕ) : ℝ) / 80) ((((60 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ≤
        hpThetaJensenCubicNeg90RectangleUpper 60 := by
  simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch060Neg90_integral_bounds

theorem hpThetaJensenCubicNeg90Batch061_integral_rectangle_bounds :
    hpThetaJensenCubicNeg90RectangleLower 61 ≤
      (∫ u : ℝ in Set.Ioo (((61 : ℕ) : ℝ) / 80) ((((61 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ∧
    (∫ u : ℝ in Set.Ioo (((61 : ℕ) : ℝ) / 80) ((((61 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ≤
        hpThetaJensenCubicNeg90RectangleUpper 61 := by
  simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch061Neg90_integral_bounds

theorem hpThetaJensenCubicNeg90Batch062_integral_rectangle_bounds :
    hpThetaJensenCubicNeg90RectangleLower 62 ≤
      (∫ u : ℝ in Set.Ioo (((62 : ℕ) : ℝ) / 80) ((((62 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ∧
    (∫ u : ℝ in Set.Ioo (((62 : ℕ) : ℝ) / 80) ((((62 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ≤
        hpThetaJensenCubicNeg90RectangleUpper 62 := by
  simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch062Neg90_integral_bounds

theorem hpThetaJensenCubicNeg90Batch063_integral_rectangle_bounds :
    hpThetaJensenCubicNeg90RectangleLower 63 ≤
      (∫ u : ℝ in Set.Ioo (((63 : ℕ) : ℝ) / 80) ((((63 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ∧
    (∫ u : ℝ in Set.Ioo (((63 : ℕ) : ℝ) / 80) ((((63 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ≤
        hpThetaJensenCubicNeg90RectangleUpper 63 := by
  simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch063Neg90_integral_bounds

theorem hpThetaJensenCubicNeg90Batch064_integral_rectangle_bounds :
    hpThetaJensenCubicNeg90RectangleLower 64 ≤
      (∫ u : ℝ in Set.Ioo (((64 : ℕ) : ℝ) / 80) ((((64 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ∧
    (∫ u : ℝ in Set.Ioo (((64 : ℕ) : ℝ) / 80) ((((64 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ≤
        hpThetaJensenCubicNeg90RectangleUpper 64 := by
  simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch064Neg90_integral_bounds

theorem hpThetaJensenCubicNeg90Batch065_integral_rectangle_bounds :
    hpThetaJensenCubicNeg90RectangleLower 65 ≤
      (∫ u : ℝ in Set.Ioo (((65 : ℕ) : ℝ) / 80) ((((65 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ∧
    (∫ u : ℝ in Set.Ioo (((65 : ℕ) : ℝ) / 80) ((((65 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ≤
        hpThetaJensenCubicNeg90RectangleUpper 65 := by
  simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch065Neg90_integral_bounds

theorem hpThetaJensenCubicNeg90Batch066_integral_rectangle_bounds :
    hpThetaJensenCubicNeg90RectangleLower 66 ≤
      (∫ u : ℝ in Set.Ioo (((66 : ℕ) : ℝ) / 80) ((((66 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ∧
    (∫ u : ℝ in Set.Ioo (((66 : ℕ) : ℝ) / 80) ((((66 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ≤
        hpThetaJensenCubicNeg90RectangleUpper 66 := by
  simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch066Neg90_integral_bounds

theorem hpThetaJensenCubicNeg90Batch067_integral_rectangle_bounds :
    hpThetaJensenCubicNeg90RectangleLower 67 ≤
      (∫ u : ℝ in Set.Ioo (((67 : ℕ) : ℝ) / 80) ((((67 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ∧
    (∫ u : ℝ in Set.Ioo (((67 : ℕ) : ℝ) / 80) ((((67 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ≤
        hpThetaJensenCubicNeg90RectangleUpper 67 := by
  simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch067Neg90_integral_bounds

theorem hpThetaJensenCubicNeg90Batch068_integral_rectangle_bounds :
    hpThetaJensenCubicNeg90RectangleLower 68 ≤
      (∫ u : ℝ in Set.Ioo (((68 : ℕ) : ℝ) / 80) ((((68 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ∧
    (∫ u : ℝ in Set.Ioo (((68 : ℕ) : ℝ) / 80) ((((68 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ≤
        hpThetaJensenCubicNeg90RectangleUpper 68 := by
  simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch068Neg90_integral_bounds

theorem hpThetaJensenCubicNeg90Batch069_integral_rectangle_bounds :
    hpThetaJensenCubicNeg90RectangleLower 69 ≤
      (∫ u : ℝ in Set.Ioo (((69 : ℕ) : ℝ) / 80) ((((69 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ∧
    (∫ u : ℝ in Set.Ioo (((69 : ℕ) : ℝ) / 80) ((((69 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ≤
        hpThetaJensenCubicNeg90RectangleUpper 69 := by
  simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch069Neg90_integral_bounds

theorem hpThetaJensenCubicNeg90Batch070_integral_rectangle_bounds :
    hpThetaJensenCubicNeg90RectangleLower 70 ≤
      (∫ u : ℝ in Set.Ioo (((70 : ℕ) : ℝ) / 80) ((((70 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ∧
    (∫ u : ℝ in Set.Ioo (((70 : ℕ) : ℝ) / 80) ((((70 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ≤
        hpThetaJensenCubicNeg90RectangleUpper 70 := by
  simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch070Neg90_integral_bounds

theorem hpThetaJensenCubicNeg90Batch071_integral_rectangle_bounds :
    hpThetaJensenCubicNeg90RectangleLower 71 ≤
      (∫ u : ℝ in Set.Ioo (((71 : ℕ) : ℝ) / 80) ((((71 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ∧
    (∫ u : ℝ in Set.Ioo (((71 : ℕ) : ℝ) / 80) ((((71 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ≤
        hpThetaJensenCubicNeg90RectangleUpper 71 := by
  simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch071Neg90_integral_bounds

theorem hpThetaJensenCubicNeg90Batch072_integral_rectangle_bounds :
    hpThetaJensenCubicNeg90RectangleLower 72 ≤
      (∫ u : ℝ in Set.Ioo (((72 : ℕ) : ℝ) / 80) ((((72 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ∧
    (∫ u : ℝ in Set.Ioo (((72 : ℕ) : ℝ) / 80) ((((72 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ≤
        hpThetaJensenCubicNeg90RectangleUpper 72 := by
  simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch072Neg90_integral_bounds

theorem hpThetaJensenCubicNeg90Batch073_integral_rectangle_bounds :
    hpThetaJensenCubicNeg90RectangleLower 73 ≤
      (∫ u : ℝ in Set.Ioo (((73 : ℕ) : ℝ) / 80) ((((73 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ∧
    (∫ u : ℝ in Set.Ioo (((73 : ℕ) : ℝ) / 80) ((((73 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ≤
        hpThetaJensenCubicNeg90RectangleUpper 73 := by
  simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch073Neg90_integral_bounds

theorem hpThetaJensenCubicNeg90Batch074_integral_rectangle_bounds :
    hpThetaJensenCubicNeg90RectangleLower 74 ≤
      (∫ u : ℝ in Set.Ioo (((74 : ℕ) : ℝ) / 80) ((((74 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ∧
    (∫ u : ℝ in Set.Ioo (((74 : ℕ) : ℝ) / 80) ((((74 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ≤
        hpThetaJensenCubicNeg90RectangleUpper 74 := by
  simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch074Neg90_integral_bounds

theorem hpThetaJensenCubicNeg90Batch075_integral_rectangle_bounds :
    hpThetaJensenCubicNeg90RectangleLower 75 ≤
      (∫ u : ℝ in Set.Ioo (((75 : ℕ) : ℝ) / 80) ((((75 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ∧
    (∫ u : ℝ in Set.Ioo (((75 : ℕ) : ℝ) / 80) ((((75 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ≤
        hpThetaJensenCubicNeg90RectangleUpper 75 := by
  simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch075Neg90_integral_bounds

theorem hpThetaJensenCubicNeg90Batch076_integral_rectangle_bounds :
    hpThetaJensenCubicNeg90RectangleLower 76 ≤
      (∫ u : ℝ in Set.Ioo (((76 : ℕ) : ℝ) / 80) ((((76 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ∧
    (∫ u : ℝ in Set.Ioo (((76 : ℕ) : ℝ) / 80) ((((76 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ≤
        hpThetaJensenCubicNeg90RectangleUpper 76 := by
  simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch076Neg90_integral_bounds

theorem hpThetaJensenCubicNeg90Batch077_integral_rectangle_bounds :
    hpThetaJensenCubicNeg90RectangleLower 77 ≤
      (∫ u : ℝ in Set.Ioo (((77 : ℕ) : ℝ) / 80) ((((77 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ∧
    (∫ u : ℝ in Set.Ioo (((77 : ℕ) : ℝ) / 80) ((((77 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ≤
        hpThetaJensenCubicNeg90RectangleUpper 77 := by
  simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch077Neg90_integral_bounds

theorem hpThetaJensenCubicNeg90Batch078_integral_rectangle_bounds :
    hpThetaJensenCubicNeg90RectangleLower 78 ≤
      (∫ u : ℝ in Set.Ioo (((78 : ℕ) : ℝ) / 80) ((((78 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ∧
    (∫ u : ℝ in Set.Ioo (((78 : ℕ) : ℝ) / 80) ((((78 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ≤
        hpThetaJensenCubicNeg90RectangleUpper 78 := by
  simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch078Neg90_integral_bounds

theorem hpThetaJensenCubicNeg90Batch079_integral_rectangle_bounds :
    hpThetaJensenCubicNeg90RectangleLower 79 ≤
      (∫ u : ℝ in Set.Ioo (((79 : ℕ) : ℝ) / 80) ((((79 : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ∧
    (∫ u : ℝ in Set.Ioo (((79 : ℕ) : ℝ) / 80) ((((79 : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ≤
        hpThetaJensenCubicNeg90RectangleUpper 79 := by
  simpa only [hpThetaJensenCubicNeg90RectangleLower, hpThetaJensenCubicNeg90RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch079Neg90_integral_bounds

theorem hpThetaJensenCubicNeg90_batchIntegral_rectangle_bounds (b : Fin 80) :
    hpThetaJensenCubicNeg90RectangleLower b.val ≤
      (∫ u : ℝ in Set.Ioo ((b.val : ℝ) / 80) (((b.val : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ∧
    (∫ u : ℝ in Set.Ioo ((b.val : ℝ) / 80) (((b.val : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-90) u) ≤
        hpThetaJensenCubicNeg90RectangleUpper b.val := by
  fin_cases b
  · exact hpThetaJensenCubicNeg90Batch000_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg90Batch001_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg90Batch002_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg90Batch003_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg90Batch004_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg90Batch005_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg90Batch006_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg90Batch007_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg90Batch008_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg90Batch009_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg90Batch010_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg90Batch011_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg90Batch012_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg90Batch013_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg90Batch014_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg90Batch015_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg90Batch016_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg90Batch017_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg90Batch018_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg90Batch019_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg90Batch020_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg90Batch021_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg90Batch022_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg90Batch023_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg90Batch024_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg90Batch025_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg90Batch026_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg90Batch027_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg90Batch028_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg90Batch029_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg90Batch030_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg90Batch031_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg90Batch032_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg90Batch033_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg90Batch034_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg90Batch035_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg90Batch036_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg90Batch037_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg90Batch038_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg90Batch039_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg90Batch040_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg90Batch041_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg90Batch042_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg90Batch043_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg90Batch044_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg90Batch045_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg90Batch046_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg90Batch047_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg90Batch048_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg90Batch049_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg90Batch050_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg90Batch051_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg90Batch052_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg90Batch053_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg90Batch054_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg90Batch055_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg90Batch056_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg90Batch057_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg90Batch058_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg90Batch059_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg90Batch060_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg90Batch061_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg90Batch062_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg90Batch063_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg90Batch064_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg90Batch065_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg90Batch066_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg90Batch067_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg90Batch068_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg90Batch069_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg90Batch070_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg90Batch071_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg90Batch072_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg90Batch073_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg90Batch074_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg90Batch075_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg90Batch076_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg90Batch077_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg90Batch078_integral_rectangle_bounds
  · exact hpThetaJensenCubicNeg90Batch079_integral_rectangle_bounds

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
