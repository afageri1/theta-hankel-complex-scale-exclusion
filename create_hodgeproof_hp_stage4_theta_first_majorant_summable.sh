#!/usr/bin/env bash
set -euo pipefail

mkdir -p HodgeProofHP

cat > HodgeProofHP/Stage4ThetaFirstMajorantSummable.lean <<'LEAN'
import HodgeProofHP.Stage4ThetaProfileLocalBound
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
Summability of the local first-derivative majorant by comparison
with a Gaussian series having half the original decay exponent.
-/

noncomputable section

namespace HodgeProofHP

theorem hpTheta_linear_factor_gaussian_bound
    (a x b r : ℝ) (ha : 0 ≤ a)
    (hx : 0 < x) (hb : 0 ≤ b) :
    ((1 / 2 : ℝ) + 2 * a * b) *
        (2 * Real.exp (r / 2 - a * x)) ≤
      (((1 / 2 : ℝ) + 4 * b / x) * Real.exp (r / 2)) *
        (2 * Real.exp (-a * (x / 2))) := by
  let y : ℝ := a * x / 2
  have hy0 : 0 ≤ y := by
    dsimp [y]
    positivity
  have hexp := Real.add_one_le_exp y
  have hy : y ≤ Real.exp y := by
    linarith
  have hone : 1 ≤ Real.exp y := by
    linarith
  have hscale_nonneg : 0 ≤ 4 * b / x := by
    positivity
  have hscale :
      (4 * b / x) * y = 2 * a * b := by
    dsimp [y]
    field_simp <;> ring
  have hweighted :=
    mul_le_mul_of_nonneg_left hy hscale_nonneg
  rw [hscale] at hweighted
  have hhalf :
      (1 / 2 : ℝ) ≤ (1 / 2 : ℝ) * Real.exp y := by
    linarith
  have hcoefficient :
      (1 / 2 : ℝ) + 2 * a * b ≤
        ((1 / 2 : ℝ) + 4 * b / x) * Real.exp y := by
    nlinarith [hweighted, hhalf]
  have hexp_product :
      Real.exp y * Real.exp (r / 2 - a * x) =
        Real.exp (r / 2) * Real.exp (-a * (x / 2)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    dsimp [y]
    ring
  calc
    ((1 / 2 : ℝ) + 2 * a * b) *
        (2 * Real.exp (r / 2 - a * x))
        ≤ (((1 / 2 : ℝ) + 4 * b / x) * Real.exp y) *
            (2 * Real.exp (r / 2 - a * x)) :=
      mul_le_mul_of_nonneg_right hcoefficient (by positivity)
    _ = (((1 / 2 : ℝ) + 4 * b / x) * 2) *
          (Real.exp y * Real.exp (r / 2 - a * x)) := by
      ring
    _ = (((1 / 2 : ℝ) + 4 * b / x) * 2) *
          (Real.exp (r / 2) * Real.exp (-a * (x / 2))) := by
      rw [hexp_product]
    _ = (((1 / 2 : ℝ) + 4 * b / x) * Real.exp (r / 2)) *
          (2 * Real.exp (-a * (x / 2))) := by
      ring

theorem hpThetaGaussianParameter_series_summable
    (x : ℝ) (hx : 0 < x) :
    Summable (fun n : ℕ =>
      2 * Real.exp (-hpThetaGaussianParameter n * x)) := by
  have h := (hpRiemannThetaKernel_hasSum x hx).summable
  simpa only [hpThetaGaussianParameter, neg_mul, mul_assoc] using h

/-- Constant used to dominate the local majorant by a Gaussian series. -/
def hpThetaGaussianFirstComparisonConstant (l r : ℝ) : ℝ :=
  ((1 / 2 : ℝ) +
      4 * Real.exp (2 * r) / Real.exp (2 * l)) *
    Real.exp (r / 2)

theorem hpThetaGaussianFirstMajorant_le_gaussian
    (l r : ℝ) (n : ℕ) :
    hpThetaGaussianFirstMajorant l r n ≤
      hpThetaGaussianFirstComparisonConstant l r *
        (2 * Real.exp
          (-hpThetaGaussianParameter n *
            (Real.exp (2 * l) / 2))) := by
  exact hpTheta_linear_factor_gaussian_bound
    (hpThetaGaussianParameter n)
    (Real.exp (2 * l))
    (Real.exp (2 * r))
    r
    (hpThetaGaussianParameter_nonneg n)
    (Real.exp_pos _)
    (Real.exp_nonneg _)

theorem hpThetaGaussianFirstMajorant_summable
    (l r : ℝ) :
    Summable (hpThetaGaussianFirstMajorant l r) := by
  have hx : 0 < Real.exp (2 * l) / 2 := by
    positivity
  have hgaussian :=
    hpThetaGaussianParameter_series_summable
      (Real.exp (2 * l) / 2) hx
  have hcomparison :
      Summable (fun n : ℕ =>
        hpThetaGaussianFirstComparisonConstant l r *
          (2 * Real.exp
            (-hpThetaGaussianParameter n *
              (Real.exp (2 * l) / 2)))) :=
    Summable.mul_left
      (hpThetaGaussianFirstComparisonConstant l r) hgaussian
  exact Summable.of_nonneg_of_le
    (fun n => hpThetaGaussianFirstMajorant_nonneg l r n)
    (fun n => hpThetaGaussianFirstMajorant_le_gaussian l r n)
    hcomparison

#print axioms hpTheta_linear_factor_gaussian_bound
#print axioms hpThetaGaussianParameter_series_summable
#print axioms hpThetaGaussianFirstMajorant_le_gaussian
#print axioms hpThetaGaussianFirstMajorant_summable

end HodgeProofHP
LEAN

lake build HodgeProofHP.Stage4ThetaProfileLocalBound
lake env lean HodgeProofHP/Stage4ThetaFirstMajorantSummable.lean
lake build HodgeProofHP.Stage4ThetaFirstMajorantSummable
