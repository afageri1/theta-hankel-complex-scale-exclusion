import HodgeProofHP.Stage4ThetaSecondLocalBound

/-!
Summability of the second-derivative majorant.
Two applications of the linear Gaussian estimate absorb the quadratic factor.
-/

noncomputable section

namespace HodgeProofHP

theorem hpTheta_quadratic_factor_gaussian_bound
    (a x b r : ℝ) (ha : 0 ≤ a)
    (hx : 0 < x) (hb : 0 ≤ b) :
    (((1 / 2 : ℝ) + 2 * a * b) ^ 2 + 4 * a * b) *
        (2 * Real.exp (r / 2 - a * x)) ≤
      (3 * (((1 / 2 : ℝ) + 4 * b / x) * Real.exp (r / 2)) *
        ((1 / 2 : ℝ) + 4 * b / (x / 2))) *
        (2 * Real.exp (-a * (x / 4))) := by
  let q : ℝ := (1 / 2 : ℝ) + 2 * a * b
  let C₁ : ℝ := (1 / 2 : ℝ) + 4 * b / x
  let C₂ : ℝ := (1 / 2 : ℝ) + 4 * b / (x / 2)
  have hq0 : 0 ≤ q := by
    dsimp [q]
    positivity
  have hC₁0 : 0 ≤ C₁ := by
    dsimp [C₁]
    positivity
  have hpoly : q ^ 2 + 4 * a * b ≤ 3 * q ^ 2 := by
    dsimp [q]
    nlinarith [sq_nonneg (a * b)]
  have h₁ :
      q * (2 * Real.exp (r / 2 - a * x)) ≤
        (C₁ * Real.exp (r / 2)) *
          (2 * Real.exp (-a * (x / 2))) :=
    hpTheta_linear_factor_gaussian_bound a x b r ha hx hb
  have hquarter : (x / 2) / 2 = x / 4 := by
    ring
  have h₂ :
      q * (2 * Real.exp (-a * (x / 2))) ≤
        C₂ * (2 * Real.exp (-a * (x / 4))) := by
    simpa only [q, C₂, zero_div, zero_sub,
      Real.exp_zero, mul_one, hquarter, neg_mul] using
      hpTheta_linear_factor_gaussian_bound
        a (x / 2) b 0 ha (by positivity) hb
  change (q ^ 2 + 4 * a * b) *
      (2 * Real.exp (r / 2 - a * x)) ≤
    (3 * (C₁ * Real.exp (r / 2)) * C₂) *
      (2 * Real.exp (-a * (x / 4)))
  calc
    (q ^ 2 + 4 * a * b) *
        (2 * Real.exp (r / 2 - a * x))
        ≤ (3 * q ^ 2) *
            (2 * Real.exp (r / 2 - a * x)) :=
      mul_le_mul_of_nonneg_right hpoly (by positivity)
    _ = (3 * q) *
          (q * (2 * Real.exp (r / 2 - a * x))) := by
      ring
    _ ≤ (3 * q) *
          ((C₁ * Real.exp (r / 2)) *
            (2 * Real.exp (-a * (x / 2)))) :=
      mul_le_mul_of_nonneg_left h₁ (by positivity)
    _ = (3 * (C₁ * Real.exp (r / 2))) *
          (q * (2 * Real.exp (-a * (x / 2)))) := by
      ring
    _ ≤ (3 * (C₁ * Real.exp (r / 2))) *
          (C₂ * (2 * Real.exp (-a * (x / 4)))) :=
      mul_le_mul_of_nonneg_left h₂ (by positivity)
    _ = (3 * (C₁ * Real.exp (r / 2)) * C₂) *
          (2 * Real.exp (-a * (x / 4))) := by
      ring

def hpThetaGaussianSecondComparisonConstant (l r : ℝ) : ℝ :=
  3 * (((1 / 2 : ℝ) +
      4 * Real.exp (2 * r) / Real.exp (2 * l)) *
      Real.exp (r / 2)) *
    ((1 / 2 : ℝ) +
      4 * Real.exp (2 * r) / (Real.exp (2 * l) / 2))

theorem hpThetaGaussianSecondMajorant_le_gaussian
    (l r : ℝ) (n : ℕ) :
    hpThetaGaussianSecondMajorant l r n ≤
      hpThetaGaussianSecondComparisonConstant l r *
        (2 * Real.exp
          (-hpThetaGaussianParameter n *
            (Real.exp (2 * l) / 4))) := by
  exact hpTheta_quadratic_factor_gaussian_bound
    (hpThetaGaussianParameter n)
    (Real.exp (2 * l))
    (Real.exp (2 * r))
    r
    (hpThetaGaussianParameter_nonneg n)
    (Real.exp_pos _)
    (Real.exp_nonneg _)

theorem hpThetaGaussianSecondMajorant_summable
    (l r : ℝ) :
    Summable (hpThetaGaussianSecondMajorant l r) := by
  have hx : 0 < Real.exp (2 * l) / 4 := by
    positivity
  have hgaussian :=
    hpThetaGaussianParameter_series_summable
      (Real.exp (2 * l) / 4) hx
  have hcomparison :
      Summable (fun n : ℕ =>
        hpThetaGaussianSecondComparisonConstant l r *
          (2 * Real.exp
            (-hpThetaGaussianParameter n *
              (Real.exp (2 * l) / 4)))) :=
    Summable.mul_left
      (hpThetaGaussianSecondComparisonConstant l r) hgaussian
  exact Summable.of_nonneg_of_le
    (fun n => hpThetaGaussianSecondMajorant_nonneg l r n)
    (fun n => hpThetaGaussianSecondMajorant_le_gaussian l r n)
    hcomparison

#print axioms hpTheta_quadratic_factor_gaussian_bound
#print axioms hpThetaGaussianSecondMajorant_le_gaussian
#print axioms hpThetaGaussianSecondMajorant_summable

end HodgeProofHP
