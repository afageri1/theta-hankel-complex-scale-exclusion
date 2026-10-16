/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenCNVGlobalPositivity
import HodgeProofHP.Stage7ThetaJensenSquareTailLogCurvature
import Mathlib.Analysis.Convex.Deriv

/-!
# Strict logarithmic concavity of the actual square-variable tail

The certified global CNV sign closes the exact logarithmic-curvature criterion.
Strict concavity also gives the equal-sum four-point inequality needed in the
moment argument. This file proves no general Turan inequality or unbounded
family of good Jensen degrees; the normalized integral comparison remains.
-/
noncomputable section
namespace HodgeProofHP

theorem hpThetaPhiSquareTail_log_secondDeriv_neg (x : ℝ) (hx : 0 < x) :
    deriv (deriv (fun y : ℝ => Real.log (hpThetaPhiSquareTail y))) x < 0 := by
  exact (hpThetaPhiSquareTail_log_secondDeriv_neg_iff_CNV x hx).mpr
    (hpThetaPhiCNVTailPositive_certified (Real.sqrt x) (Real.sqrt_pos.mpr hx))

theorem hpThetaPhiSquareTail_log_strictConcaveOn :
    StrictConcaveOn ℝ (Set.Ioi (0 : ℝ))
      (fun x : ℝ => Real.log (hpThetaPhiSquareTail x)) := by
  apply strictConcaveOn_of_deriv2_neg' (convex_Ioi (0 : ℝ))
  · intro x hx
    have hx0 : 0 < x := by simpa only [Set.mem_Ioi] using hx
    exact (hpThetaPhiSquareTail_log_hasDerivAt x hx0).continuousAt.continuousWithinAt
  · intro x hx
    have hx0 : 0 < x := by simpa only [Set.mem_Ioi] using hx
    change deriv (deriv (fun y : ℝ => Real.log (hpThetaPhiSquareTail y))) x < 0
    exact hpThetaPhiSquareTail_log_secondDeriv_neg x hx0

theorem hpThetaPhiSquareTailLogSlope_strictAntiOn :
    StrictAntiOn hpThetaPhiSquareTailLogSlope (Set.Ioi (0 : ℝ)) := by
  have hanti := hpThetaPhiSquareTail_log_strictConcaveOn.strictAntiOn_deriv
    (fun x hx => (hpThetaPhiSquareTail_log_hasDerivAt x hx).differentiableAt)
  intro x hx y hy hxy
  have h := hanti hx hy hxy
  rw [hpThetaPhiSquareTail_log_deriv x hx, hpThetaPhiSquareTail_log_deriv y hy] at h
  exact h

theorem hpThetaPhiSquareTail_log_fourPoint (a c d b : ℝ)
    (ha : 0 < a) (hac : a < c) (hcd : c < d) (hdb : d < b)
    (hsum : c + d = a + b) :
    Real.log (hpThetaPhiSquareTail a) + Real.log (hpThetaPhiSquareTail b) <
      Real.log (hpThetaPhiSquareTail c) + Real.log (hpThetaPhiSquareTail d) := by
  have hab : a < b := hac.trans (hcd.trans hdb)
  have hcb : c < b := hcd.trans hdb
  have hb : 0 < b := ha.trans hab
  have hden : 0 < b - a := sub_pos.mpr hab
  have hden0 : b - a ≠ 0 := ne_of_gt hden
  let p : ℝ := (b - c) / (b - a)
  let q : ℝ := (c - a) / (b - a)
  have hp : 0 < p := div_pos (sub_pos.mpr hcb) hden
  have hq : 0 < q := div_pos (sub_pos.mpr hac) hden
  have hpq : p + q = 1 := by
    dsimp [p, q]
    field_simp [hden0]
    <;> ring
  have hmixc : p * a + q * b = c := by
    dsimp [p, q]
    field_simp [hden0]
    <;> ring
  have hmixd : q * a + p * b = d := by
    calc
      q * a + p * b = a + b - c := by
        dsimp [p, q]
        field_simp [hden0]
        <;> ring
      _ = d := by linarith [hsum]
  have hc := hpThetaPhiSquareTail_log_strictConcaveOn.2
    (show a ∈ Set.Ioi (0 : ℝ) from ha)
    (show b ∈ Set.Ioi (0 : ℝ) from hb) (ne_of_lt hab) hp hq hpq
  have hd := hpThetaPhiSquareTail_log_strictConcaveOn.2
    (show a ∈ Set.Ioi (0 : ℝ) from ha)
    (show b ∈ Set.Ioi (0 : ℝ) from hb) (ne_of_lt hab) hq hp (by linarith [hpq])
  simp only [smul_eq_mul, hmixc] at hc
  simp only [smul_eq_mul, hmixd] at hd
  have heq :
      p * Real.log (hpThetaPhiSquareTail a) + q * Real.log (hpThetaPhiSquareTail b) +
        (q * Real.log (hpThetaPhiSquareTail a) + p * Real.log (hpThetaPhiSquareTail b)) =
      Real.log (hpThetaPhiSquareTail a) + Real.log (hpThetaPhiSquareTail b) := by
    calc
      _ = (p + q) *
          (Real.log (hpThetaPhiSquareTail a) + Real.log (hpThetaPhiSquareTail b)) := by ring
      _ = _ := by rw [hpq, one_mul]
  linarith

theorem hpThetaPhiSquareTail_fourPoint_product (a c d b : ℝ)
    (ha : 0 < a) (hac : a < c) (hcd : c < d) (hdb : d < b)
    (hsum : c + d = a + b) :
    hpThetaPhiSquareTail a * hpThetaPhiSquareTail b <
      hpThetaPhiSquareTail c * hpThetaPhiSquareTail d := by
  have hc : 0 < c := ha.trans hac
  have hd : 0 < d := hc.trans hcd
  have hb : 0 < b := hd.trans hdb
  have h := Real.exp_lt_exp.mpr (hpThetaPhiSquareTail_log_fourPoint a c d b ha hac hcd hdb hsum)
  simpa only [Real.exp_add,
    Real.exp_log (hpThetaPhiSquareTail_pos a ha),
    Real.exp_log (hpThetaPhiSquareTail_pos b hb),
    Real.exp_log (hpThetaPhiSquareTail_pos c hc),
    Real.exp_log (hpThetaPhiSquareTail_pos d hd)] using h

#print axioms hpThetaPhiSquareTail_log_secondDeriv_neg
#print axioms hpThetaPhiSquareTail_log_strictConcaveOn
#print axioms hpThetaPhiSquareTailLogSlope_strictAntiOn
#print axioms hpThetaPhiSquareTail_log_fourPoint
#print axioms hpThetaPhiSquareTail_fourPoint_product
end HodgeProofHP
