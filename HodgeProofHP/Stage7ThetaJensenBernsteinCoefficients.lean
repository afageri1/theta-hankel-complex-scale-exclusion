/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenBernsteinBounds

/-!
# Exact degree-six Bernstein coefficients of the cubic weight

For u = a + h*t, elevate the powers u^2 and u^4 to degree six and
expand u^6. The formula uses only rational constants and natural
binomial coefficients, so it can be instantiated on rational cells.
No numerical coefficient enclosure or evaluation sign is asserted.
-/
noncomputable section
namespace HodgeProofHP

def hpThetaBernsteinPowerTwo (a h : ℝ) (k : Fin 7) : ℝ :=
  a ^ 2 + (k.val : ℝ) / 3 * a * h + (k.val.choose 2 : ℝ) / 15 * h ^ 2

def hpThetaBernsteinPowerFour (a h : ℝ) (k : Fin 7) : ℝ :=
  a ^ 4 + (2 * (k.val : ℝ) / 3) * a ^ 3 * h +
    (2 * (k.val.choose 2 : ℝ) / 5) * a ^ 2 * h ^ 2 +
    (k.val.choose 3 : ℝ) / 5 * a * h ^ 3 +
    (k.val.choose 4 : ℝ) / 15 * h ^ 4

def hpThetaBernsteinPowerSix (a h : ℝ) (k : Fin 7) : ℝ :=
  a ^ 6 + (k.val : ℝ) * a ^ 5 * h +
    (k.val.choose 2 : ℝ) * a ^ 4 * h ^ 2 +
    (k.val.choose 3 : ℝ) * a ^ 3 * h ^ 3 +
    (k.val.choose 4 : ℝ) * a ^ 2 * h ^ 4 +
    (k.val.choose 5 : ℝ) * a * h ^ 5 + (k.val.choose 6 : ℝ) * h ^ 6

def hpThetaJensenCubicBernsteinCoefficient (p a h : ℝ) (k : Fin 7) : ℝ :=
  1 + (3 * p / 2) * hpThetaBernsteinPowerTwo a h k +
    (p ^ 2 / 4) * hpThetaBernsteinPowerFour a h k +
    (p ^ 3 / 120) * hpThetaBernsteinPowerSix a h k

theorem hpThetaJensenCubicWeight_bernstein_expansion (p a h t : ℝ) :
    hpThetaBernsteinValue 6 (hpThetaJensenCubicBernsteinCoefficient p a h) t =
      hpThetaJensenCubicWeight p (a + h * t) := by
  norm_num [hpThetaBernsteinValue, hpThetaJensenCubicBernsteinCoefficient,
    hpThetaBernsteinPowerTwo, hpThetaBernsteinPowerFour, hpThetaBernsteinPowerSix,
    hpThetaJensenCubicWeight, Fin.sum_univ_succ]
  ring

theorem hpThetaJensenCubicWeight_bernstein_cell (p a b u : ℝ) (hab : a < b) :
    hpThetaJensenCubicWeight p u =
      hpThetaBernsteinValue 6 (hpThetaJensenCubicBernsteinCoefficient p a (b - a))
        ((u - a) / (b - a)) := by
  rw [hpThetaJensenCubicWeight_bernstein_expansion]
  have hden : b - a ≠ 0 := ne_of_gt (sub_pos.mpr hab)
  have hu : a + (b - a) * ((u - a) / (b - a)) = u := by
    field_simp [hden] <;> ring
  rw [hu]

theorem hpThetaJensenCubicWeight_bounds_of_coefficients
    (p a b u L U : ℝ) (hab : a < b) (hu : u ∈ Set.Icc a b)
    (hc : ∀ k : Fin 7,
      L ≤ hpThetaJensenCubicBernsteinCoefficient p a (b - a) k ∧
        hpThetaJensenCubicBernsteinCoefficient p a (b - a) k ≤ U) :
    L ≤ hpThetaJensenCubicWeight p u ∧ hpThetaJensenCubicWeight p u ≤ U := by
  exact hpThetaJensenCubicWeight_bounds_of_bernstein p a b u L U
    (hpThetaJensenCubicBernsteinCoefficient p a (b - a)) hab hu hc
    (hpThetaJensenCubicWeight_bernstein_cell p a b u hab)

#print axioms hpThetaJensenCubicWeight_bernstein_expansion
#print axioms hpThetaJensenCubicWeight_bernstein_cell
#print axioms hpThetaJensenCubicWeight_bounds_of_coefficients
end HodgeProofHP
