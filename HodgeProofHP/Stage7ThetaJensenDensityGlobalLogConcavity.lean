/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenDensityOuterPositivity

/-! Join compact certificates and analytic outer bounds for the actual density. -/
noncomputable section
namespace HodgeProofHP

theorem hpThetaPhiDensityCurvature_pos_global (t : ℝ) (ht : 0 < t) :
    0 < hpThetaPhiDensityCurvature t := by
  by_cases hhalf : t ≤ (1 / 2 : ℝ)
  · exact hpThetaPhiDensityCurvature_pos_on_connected_half t ⟨ht, hhalf⟩
  · exact hpThetaPhiDensityCurvature_pos_on_outer_half t (lt_of_not_ge hhalf).le

theorem hpThetaPhiSquareDensity_log_secondDeriv_neg_global (x : ℝ) (hx : 0 < x) :
    deriv (deriv (fun y : ℝ => Real.log (hpThetaPhiSquareDensity y))) x < 0 := by
  exact (hpThetaPhiSquareDensity_log_secondDeriv_neg_iff x hx).mpr
    (hpThetaPhiDensityCurvature_pos_global (Real.sqrt x) (Real.sqrt_pos.mpr hx))

theorem hpThetaPhiSquareDensity_log_strictConcaveOn_global :
    StrictConcaveOn ℝ (Set.Ioi (0 : ℝ))
      (fun x : ℝ => Real.log (hpThetaPhiSquareDensity x)) := by
  exact hpThetaPhiSquareDensity_log_strictConcaveOn_of_curvature
    hpThetaPhiDensityCurvature_pos_global

theorem hpThetaPhiDensityNormalizedSlope_strictAntiOn_global :
    StrictAntiOn hpThetaPhiDensityNormalizedSlope (Set.Ioi (0 : ℝ)) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi (0 : ℝ))
  · intro t ht
    exact (hpThetaPhiDensityNormalizedSlope_hasDerivAt t ht).continuousAt.continuousWithinAt
  · intro t ht
    have ht' : t ∈ Set.Ioi (0 : ℝ) := interior_subset ht
    rw [(hpThetaPhiDensityNormalizedSlope_hasDerivAt t ht').deriv]
    have hL := hpThetaPhiDensityCurvature_pos_global t ht'
    have hphi := hpThetaPhi_pos_on_nonnegative t ht'.le
    exact div_neg_of_neg_of_pos (by linarith) (sq_pos_of_pos (mul_pos ht' hphi))

#print axioms hpThetaPhiDensityCurvature_pos_global
#print axioms hpThetaPhiSquareDensity_log_secondDeriv_neg_global
#print axioms hpThetaPhiSquareDensity_log_strictConcaveOn_global
#print axioms hpThetaPhiDensityNormalizedSlope_strictAntiOn_global
end HodgeProofHP
