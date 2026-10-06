import HodgeProofHP.Stage4ThetaTraceIntervalLowerBound
import Mathlib.Analysis.Real.Pi.Bounds

/-!
Explicit endpoint lower bounds for the first theta term.
No numerical exponential estimates are assumed or imported.
-/

namespace HodgeProofHP

open MeasureTheory

noncomputable def hpThetaTraceEndpointLower (l r : ℝ) : ℝ :=
  (4 * (Real.pi * Real.exp (2 * l)) ^ 2 -
    6 * (Real.pi * Real.exp (2 * l))) *
    (2 * Real.exp (l / 2 - Real.pi * Real.exp (2 * r)))

theorem hpThetaTrace_pi_exp_ge_three
    (u : ℝ) (hu : 0 ≤ u) :
    3 ≤ Real.pi * Real.exp (2 * u) := by
  have hexp : 1 ≤ Real.exp (2 * u) := by
    have h := Real.add_one_le_exp (2 * u)
    linarith
  calc
    3 ≤ Real.pi := le_of_lt Real.pi_gt_three
    _ = Real.pi * 1 := by ring
    _ ≤ Real.pi * Real.exp (2 * u) :=
      mul_le_mul_of_nonneg_left hexp (le_of_lt Real.pi_pos)

theorem hpThetaTrace_scalar_polynomial_mono
    (s t : ℝ) (hs : 3 ≤ s) (hst : s ≤ t) :
    4 * s ^ 2 - 6 * s ≤ 4 * t ^ 2 - 6 * t := by
  have hfactor : 0 ≤ 4 * (t + s) - 6 := by
    linarith
  have hprod :=
    mul_nonneg (sub_nonneg.mpr hst) hfactor
  nlinarith

theorem hpThetaTraceEndpointLower_nonneg
    (l r : ℝ) (hl : 0 ≤ l) :
    0 ≤ hpThetaTraceEndpointLower l r := by
  have hs := hpThetaTrace_pi_exp_ge_three l hl
  have hpoly :
      0 ≤ 4 * (Real.pi * Real.exp (2 * l)) ^ 2 -
        6 * (Real.pi * Real.exp (2 * l)) := by
    have hprod := mul_nonneg
      (show 0 ≤ Real.pi * Real.exp (2 * l) by linarith)
      (show 0 ≤ 4 * (Real.pi * Real.exp (2 * l)) - 6 by
        linarith)
    nlinarith
  unfold hpThetaTraceEndpointLower
  exact mul_nonneg hpoly
    (mul_nonneg (by norm_num)
      (le_of_lt (Real.exp_pos _)))

theorem hpThetaTraceEndpointLower_le_firstTerm
    (l r u : ℝ) (hl : 0 ≤ l)
    (hlu : l ≤ u) (hur : u ≤ r) :
    hpThetaTraceEndpointLower l r ≤ hpThetaTraceFirstTerm u := by
  have hel : Real.exp (2 * l) ≤ Real.exp (2 * u) :=
    Real.exp_le_exp.mpr (by linarith)
  have her : Real.exp (2 * u) ≤ Real.exp (2 * r) :=
    Real.exp_le_exp.mpr (by linarith)
  have htl :
      Real.pi * Real.exp (2 * l) ≤
        Real.pi * Real.exp (2 * u) :=
    mul_le_mul_of_nonneg_left hel (le_of_lt Real.pi_pos)
  have htr :
      Real.pi * Real.exp (2 * u) ≤
        Real.pi * Real.exp (2 * r) :=
    mul_le_mul_of_nonneg_left her (le_of_lt Real.pi_pos)
  have hs := hpThetaTrace_pi_exp_ge_three l hl
  have hpoly := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (2 * l))
    (Real.pi * Real.exp (2 * u)) hs htl
  have hpoly0 :
      0 ≤ 4 * (Real.pi * Real.exp (2 * u)) ^ 2 -
        6 * (Real.pi * Real.exp (2 * u)) := by
    have ht : 3 ≤ Real.pi * Real.exp (2 * u) :=
      le_trans hs htl
    have hprod := mul_nonneg
      (show 0 ≤ Real.pi * Real.exp (2 * u) by linarith)
      (show 0 ≤ 4 * (Real.pi * Real.exp (2 * u)) - 6 by
        linarith)
    nlinarith
  have hexp :
      2 * Real.exp (l / 2 - Real.pi * Real.exp (2 * r)) ≤
        2 * Real.exp (u / 2 - Real.pi * Real.exp (2 * u)) := by
    apply mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by linarith))
      (by norm_num)
  unfold hpThetaTraceEndpointLower
  calc
    _ ≤ (4 * (Real.pi * Real.exp (2 * u)) ^ 2 -
          6 * (Real.pi * Real.exp (2 * u))) *
          (2 * Real.exp (u / 2 - Real.pi * Real.exp (2 * u))) :=
      mul_le_mul hpoly hexp
        (mul_nonneg (by norm_num)
          (le_of_lt (Real.exp_pos _))) hpoly0
    _ = hpThetaTraceFirstTerm u := by
      rw [hpThetaTraceFirstTerm_explicit]
      ring

theorem hpThetaTraceEndpointLower_energy_le
    (l r : ℝ) (hl : 0 ≤ l) (hlr : l ≤ r) :
    l * hpThetaTraceEndpointLower l r ^ 2 * (r - l) ≤
      hpThetaFirstTraceEnergy := by
  apply hpThetaTraceFirstTerm_interval_lower_le_totalEnergy
    l r (hpThetaTraceEndpointLower l r) hl hlr
    (hpThetaTraceEndpointLower_nonneg l r hl)
  intro u hu
  exact hpThetaTraceEndpointLower_le_firstTerm
    l r u hl (le_of_lt hu.1) (le_of_lt hu.2)

#print axioms hpThetaTrace_pi_exp_ge_three
#print axioms hpThetaTrace_scalar_polynomial_mono
#print axioms hpThetaTraceEndpointLower_nonneg
#print axioms hpThetaTraceEndpointLower_le_firstTerm
#print axioms hpThetaTraceEndpointLower_energy_le

end HodgeProofHP
