/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenDensityScoreIntegrability

/-!
# Unconditional real density moment comparisons

Every required score-weighted integral is proved integrable in the imported file.
The resulting strict moment inequality holds for every real center p > 0.
Half-integer specialization recovers weighted even theta moment inequalities.
No cubic higher Turan gap sign is asserted.
-/
noncomputable section
open MeasureTheory
namespace HodgeProofHP

theorem hpThetaDensity_rpowWeight_mul_x (p x : ℝ) (hx : 0 < x) :
    x * (x ^ p * hpThetaPhiSquareDensity x) =
      x ^ (p + 1) * hpThetaPhiSquareDensity x := by
  rw [Real.rpow_add hx, Real.rpow_one]
  ring

theorem hpThetaDensityRealMoment_strict_inequality (p : ℝ) (hp : 0 < p) :
    p * hpThetaDensityRealMoment (p - 1) * hpThetaDensityRealMoment (p + 1) <
      (p + 1) * hpThetaDensityRealMoment p ^ 2 := by
  let w : ℝ → ℝ := fun x => x ^ p * hpThetaPhiSquareDensity x
  have hw : IntegrableOn w (Set.Ioi 0) volume :=
    hpThetaPhiSquareDensity_rpowMoment_integrableOn p (by linarith)
  have hxw : IntegrableOn (fun x : ℝ => x * w x) (Set.Ioi 0) volume := by
    apply Integrable.congr (hpThetaPhiSquareDensity_rpowMoment_integrableOn (p + 1)
      (by linarith))
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact (hpThetaDensity_rpowWeight_mul_x p x hx).symm
  have hxqw : IntegrableOn (fun x : ℝ => x * hpThetaDensityScore x * w x)
      (Set.Ioi 0) volume := by
    apply Integrable.congr (hpThetaDensityScore_rpowWeight_integrableOn (p + 1)
      (by linarith))
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [← hpThetaDensity_rpowWeight_mul_x p x hx]
    dsimp [w]
    ring
  have h := hpThetaDensityScore_weighted_integral_comparison w hw hxw
    (hpThetaDensityScore_rpowWeight_integrableOn p hp) hxqw
    (fun x hx => mul_pos (Real.rpow_pos_of_pos hx _) (hpThetaPhiSquareDensity_pos x hx))
  have hxmass : (∫ x in Set.Ioi (0 : ℝ), x * w x) =
      hpThetaDensityRealMoment (p + 1) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    exact hpThetaDensity_rpowWeight_mul_x p x hx
  have hxqmass : (∫ x in Set.Ioi (0 : ℝ), x * hpThetaDensityScore x * w x) =
      (p + 1) * hpThetaDensityRealMoment p := by
    calc
      _ = ∫ x in Set.Ioi (0 : ℝ), hpThetaDensityScore x *
          (x ^ (p + 1) * hpThetaPhiSquareDensity x) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x hx
        change x * hpThetaDensityScore x * w x =
          hpThetaDensityScore x * (x ^ (p + 1) * hpThetaPhiSquareDensity x)
        rw [← hpThetaDensity_rpowWeight_mul_x p x hx]
        dsimp [w]
        ring
      _ = (p + 1) * hpThetaDensityRealMoment ((p + 1) - 1) :=
        hpThetaDensityScore_rpowWeight_integral (p + 1) (by linarith)
      _ = _ := by rw [show (p + 1) - 1 = p by ring]
  change (∫ x in Set.Ioi (0 : ℝ), x * w x) *
      (∫ x in Set.Ioi (0 : ℝ), hpThetaDensityScore x *
        (x ^ p * hpThetaPhiSquareDensity x)) <
    hpThetaDensityRealMoment p *
      (∫ x in Set.Ioi (0 : ℝ), x * hpThetaDensityScore x * w x) at h
  rw [hxmass, hpThetaDensityScore_rpowWeight_integral p hp, hxqmass] at h
  nlinarith only [h]

theorem hpThetaDensity_evenMoment_strict_inequality (n : ℕ) :
    ((n : ℝ) + 1 / 2) * hpThetaPhiEvenMoment n * hpThetaPhiEvenMoment (n + 2) <
      ((n : ℝ) + 3 / 2) * hpThetaPhiEvenMoment (n + 1) ^ 2 := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have h := hpThetaDensityRealMoment_strict_inequality ((n : ℝ) + 1 / 2)
    (by linarith)
  have he0 : ((n : ℝ) + 1 / 2) - 1 = (n : ℝ) - 1 / 2 := by ring
  have he1 : (n : ℝ) + 1 / 2 = ((n + 1 : ℕ) : ℝ) - 1 / 2 := by push_cast; ring
  have he2 : ((n : ℝ) + 1 / 2) + 1 = ((n + 2 : ℕ) : ℝ) - 1 / 2 := by push_cast; ring
  rw [he0, he2] at h
  -- Change only the central moment's argument; the coefficient is unchanged.
  have hcenter : hpThetaDensityRealMoment ((n : ℝ) + 1 / 2) =
      2 * hpThetaPhiEvenMoment (n + 1) := by
    rw [he1]
    exact hpThetaDensityRealMoment_half_eq_evenMoment (n + 1)
  rw [hpThetaDensityRealMoment_half_eq_evenMoment n,
    hpThetaDensityRealMoment_half_eq_evenMoment (n + 2), hcenter] at h
  push_cast at h
  nlinarith only [h]

#print axioms hpThetaDensity_rpowWeight_mul_x
#print axioms hpThetaDensityRealMoment_strict_inequality
#print axioms hpThetaDensity_evenMoment_strict_inequality
end HodgeProofHP
