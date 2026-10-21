/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftThreeIntegral
import HodgeProofHP.Stage7ThetaJensenBernsteinBounds

/-! Thirteen Bernstein coefficients for the degree-twelve shift-three integral weight.
Numerical cell certificates and shift-three hyperbolicity remain separate targets. -/
noncomputable section
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftThreeBernsteinPower (m : ℕ) (a h : ℝ) (k : Fin 13) : ℝ :=
  ∑ j ∈ Finset.range (m + 1),
    (m.choose j : ℝ) * (k.val.choose j : ℝ) / ((12 : ℕ).choose j : ℝ) *
      a ^ (m - j) * h ^ j

def hpThetaJensenShiftThreeBernsteinCoefficient (p a h : ℝ) (k : Fin 13) : ℝ :=
  (1 / 120) * hpThetaShiftThreeBernsteinPower 6 a h k +
    (p / 560) * hpThetaShiftThreeBernsteinPower 8 a h k +
    (p ^ 2 / 10080) * hpThetaShiftThreeBernsteinPower 10 a h k +
    (p ^ 3 / 665280) * hpThetaShiftThreeBernsteinPower 12 a h k

set_option maxHeartbeats 20000000 in
-- Expand thirteen basis terms and check their exact degree-twelve polynomial identity.
theorem hpThetaJensenShiftThreeWeight_bernstein_expansion (p a h t : ℝ) :
    hpThetaBernsteinValue 12 (hpThetaJensenShiftThreeBernsteinCoefficient p a h) t =
      hpThetaJensenShiftThreeWeight p (a + h * t) := by
  norm_num [hpThetaBernsteinValue, Fin.sum_univ_succ,
    hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
    Finset.sum_range_succ, hpThetaJensenShiftThreeWeight, Nat.choose]
  <;> ring

theorem hpThetaJensenShiftThreeWeight_bernstein_cell (p a b u : ℝ) (hab : a < b) :
    hpThetaJensenShiftThreeWeight p u =
      hpThetaBernsteinValue 12 (hpThetaJensenShiftThreeBernsteinCoefficient p a (b - a))
        ((u - a) / (b - a)) := by
  rw [hpThetaJensenShiftThreeWeight_bernstein_expansion]
  have hden : b - a ≠ 0 := ne_of_gt (sub_pos.mpr hab)
  have hu : a + (b - a) * ((u - a) / (b - a)) = u := by
    field_simp [hden] <;> ring
  rw [hu]

theorem hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (p a b u L U : ℝ) (hab : a < b) (hu : u ∈ Set.Icc a b)
    (hc : ∀ k : Fin 13,
      L ≤ hpThetaJensenShiftThreeBernsteinCoefficient p a (b - a) k ∧
        hpThetaJensenShiftThreeBernsteinCoefficient p a (b - a) k ≤ U) :
    L ≤ hpThetaJensenShiftThreeWeight p u ∧ hpThetaJensenShiftThreeWeight p u ≤ U := by
  have hden : 0 < b - a := sub_pos.mpr hab
  have hx : (u - a) / (b - a) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (sub_nonneg.mpr hu.1) hden.le
    · exact (div_le_one hden).2 (sub_le_sub_right hu.2 a)
  rw [hpThetaJensenShiftThreeWeight_bernstein_cell p a b u hab]
  exact hpThetaBernsteinValue_bounds 12 _ L U _ hx hc

#print axioms hpThetaJensenShiftThreeWeight_bernstein_expansion
#print axioms hpThetaJensenShiftThreeWeight_bernstein_cell
#print axioms hpThetaJensenShiftThreeWeight_bounds_of_coefficients
end HodgeProofHP
