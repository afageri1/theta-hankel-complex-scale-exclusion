/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenCNVSquareTailRealMoments
import HodgeProofHP.Stage7ThetaJensenCNVRightDerivative

/-!
# The actual theta-to-tail moment identity

Substitution x = t^2 transfers the square-tail integrability to all natural
moments of the weighted tail. The product t^(m+1) I(t) and its derivative are
integrable, so that product tends to zero at infinity. Improper integration
by parts then identifies the half-integer square-tail moments with the even
theta moments, including the factor 4/(2n+1).

The normalized moment comparison and general Turan inequalities are not
asserted by this file.
-/
noncomputable section
open Filter MeasureTheory
open scoped Topology
namespace HodgeProofHP

theorem hpThetaCNV_squareSubstitution_factor (m : ℕ) (t : ℝ) (ht : 0 < t) :
    t ^ ((2 : ℝ) - 1) *
        ((t ^ (2 : ℝ)) ^ (((m : ℝ) - 1) / 2) *
          hpThetaPhiSquareTail (t ^ (2 : ℝ))) =
      2 * (t ^ m * hpThetaPhiWeightedTail t) := by
  have hpow : t * (t ^ (2 : ℝ)) ^ (((m : ℝ) - 1) / 2) = t ^ m := by
    rw [← Real.rpow_mul ht.le]
    calc
      t * t ^ (2 * (((m : ℝ) - 1) / 2)) =
          t ^ (1 + 2 * (((m : ℝ) - 1) / 2)) := by
        rw [Real.rpow_add ht, Real.rpow_one]
      _ = t ^ (m : ℝ) := by congr 1; ring
      _ = t ^ m := Real.rpow_natCast t m
  have hK : hpThetaPhiSquareTail (t ^ (2 : ℝ)) =
      2 * hpThetaPhiWeightedTail t := by
    rw [Real.rpow_natCast t 2]
    simp only [hpThetaPhiSquareTail, Real.sqrt_sq_eq_abs, abs_of_pos ht]
  rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, hK]
  calc
    t * ((t ^ (2 : ℝ)) ^ (((m : ℝ) - 1) / 2) *
        (2 * hpThetaPhiWeightedTail t)) =
        2 * ((t * (t ^ (2 : ℝ)) ^ (((m : ℝ) - 1) / 2)) *
          hpThetaPhiWeightedTail t) := by ring
    _ = 2 * (t ^ m * hpThetaPhiWeightedTail t) := by rw [hpow]

theorem hpThetaPhiWeightedTail_natMoment_integrableOn (m : ℕ) :
    IntegrableOn (fun t : ℝ => t ^ m * hpThetaPhiWeightedTail t)
      (Set.Ioi 0) volume := by
  have hp : -1 < ((m : ℝ) - 1) / 2 := by
    have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hs := (MeasureTheory.integrableOn_Ioi_comp_rpow_iff'
    (fun x : ℝ => x ^ (((m : ℝ) - 1) / 2) * hpThetaPhiSquareTail x)
    (p := 2) (by norm_num)).mpr
      (hpThetaPhiSquareTail_rpowMoment_integrableOn _ hp)
  have htwo : IntegrableOn (fun t : ℝ => 2 * (t ^ m * hpThetaPhiWeightedTail t))
      (Set.Ioi 0) volume := by
    apply Integrable.congr hs
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simpa only [smul_eq_mul] using hpThetaCNV_squareSubstitution_factor m t ht
  apply Integrable.congr (htwo.const_mul (1 / 2 : ℝ))
  filter_upwards [] with t
  ring

theorem hpThetaCNV_tailMomentProduct_hasDerivAt (m : ℕ) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun u : ℝ => u ^ (m + 1) * hpThetaPhiWeightedTail u)
      (((m : ℝ) + 1) * (t ^ m * hpThetaPhiWeightedTail t) -
        t ^ (m + 2) * hpRiemannThetaDifferentialKernel t) t := by
  have h := ((hasDerivAt_id t).pow (m + 1)).mul
    (hpThetaPhiWeightedTail_hasDerivAt t ht)
  convert h using 1 <;>
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, pow_succ] <;> ring

theorem hpThetaCNV_tailMomentProduct_derivative_integrableOn (m : ℕ) :
    IntegrableOn (fun t : ℝ =>
      ((m : ℝ) + 1) * (t ^ m * hpThetaPhiWeightedTail t) -
        t ^ (m + 2) * hpRiemannThetaDifferentialKernel t) (Set.Ioi 0) volume := by
  exact ((hpThetaPhiWeightedTail_natMoment_integrableOn m).const_mul
    ((m : ℝ) + 1)).sub (hpThetaPhi_natMoment_integrableOn (m + 2))

theorem hpThetaCNV_tailMomentProduct_tendsto_zero (m : ℕ) :
    Tendsto (fun t : ℝ => t ^ (m + 1) * hpThetaPhiWeightedTail t) atTop (𝓝 0) := by
  exact MeasureTheory.tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi
    (fun t ht => hpThetaCNV_tailMomentProduct_hasDerivAt m t ht)
    (hpThetaCNV_tailMomentProduct_derivative_integrableOn m)
    (hpThetaPhiWeightedTail_natMoment_integrableOn (m + 1))

theorem hpThetaPhiWeightedTail_natMoment_eq (m : ℕ) :
    (∫ t in Set.Ioi (0 : ℝ), t ^ m * hpThetaPhiWeightedTail t) =
      (∫ t in Set.Ioi (0 : ℝ), t ^ (m + 2) * hpRiemannThetaDifferentialKernel t) /
        ((m : ℝ) + 1) := by
  have hc : ContinuousWithinAt
      (fun t : ℝ => t ^ (m + 1) * hpThetaPhiWeightedTail t) (Set.Ici 0) 0 :=
    (continuous_id.pow (m + 1)).continuousWithinAt.mul
      hpThetaPhiWeightedTail_hasDerivWithinAt_zero.continuousWithinAt
  have h := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto hc
    (fun t ht => hpThetaCNV_tailMomentProduct_hasDerivAt m t ht)
    (hpThetaCNV_tailMomentProduct_derivative_integrableOn m)
    (hpThetaCNV_tailMomentProduct_tendsto_zero m)
  rw [integral_sub
    ((hpThetaPhiWeightedTail_natMoment_integrableOn m).const_mul ((m : ℝ) + 1))
    (hpThetaPhi_natMoment_integrableOn (m + 2)), integral_const_mul] at h
  simp only [zero_pow (by omega : m + 1 ≠ 0), zero_mul, sub_zero] at h
  apply (eq_div_iff (by positivity : (m : ℝ) + 1 ≠ 0)).mpr
  nlinarith [h]

theorem hpThetaPhiSquareTail_rpowMoment_substitution (m : ℕ) :
    (∫ x in Set.Ioi (0 : ℝ),
      x ^ (((m : ℝ) - 1) / 2) * hpThetaPhiSquareTail x) =
      4 * ∫ t in Set.Ioi (0 : ℝ), t ^ m * hpThetaPhiWeightedTail t := by
  have hs := MeasureTheory.integral_comp_rpow_Ioi_of_pos
    (g := fun x : ℝ => x ^ (((m : ℝ) - 1) / 2) * hpThetaPhiSquareTail x)
    (p := 2) (by norm_num)
  calc
    _ = ∫ t in Set.Ioi (0 : ℝ),
        (2 * t ^ ((2 : ℝ) - 1)) •
          ((t ^ (2 : ℝ)) ^ (((m : ℝ) - 1) / 2) *
            hpThetaPhiSquareTail (t ^ (2 : ℝ))) := hs.symm
    _ = ∫ t in Set.Ioi (0 : ℝ), 4 * (t ^ m * hpThetaPhiWeightedTail t) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      simp only [smul_eq_mul]
      calc
        _ = 2 * (t ^ ((2 : ℝ) - 1) *
            ((t ^ (2 : ℝ)) ^ (((m : ℝ) - 1) / 2) *
              hpThetaPhiSquareTail (t ^ (2 : ℝ)))) := by ring
        _ = 4 * (t ^ m * hpThetaPhiWeightedTail t) := by
          rw [hpThetaCNV_squareSubstitution_factor m t ht]
          ring
    _ = _ := integral_const_mul _ _

theorem hpThetaPhiSquareTail_halfMoment_eq_evenMoment (n : ℕ) :
    (∫ x in Set.Ioi (0 : ℝ),
      x ^ ((n : ℝ) - 1 / 2) * hpThetaPhiSquareTail x) =
      4 / (2 * (n : ℝ) + 1) * hpThetaPhiEvenMoment (n + 1) := by
  have hexponent : (((2 * n : ℕ) : ℝ) - 1) / 2 = (n : ℝ) - 1 / 2 := by
    push_cast
    ring
  have h := hpThetaPhiSquareTail_rpowMoment_substitution (2 * n)
  rw [hexponent, hpThetaPhiWeightedTail_natMoment_eq] at h
  have hindex : 2 * n + 2 = 2 * (n + 1) := by omega
  rw [hindex] at h
  change (∫ x in Set.Ioi (0 : ℝ),
      x ^ ((n : ℝ) - 1 / 2) * hpThetaPhiSquareTail x) =
    4 * (hpThetaPhiEvenMoment (n + 1) / (((2 * n : ℕ) : ℝ) + 1)) at h
  rw [h]
  push_cast
  ring

#print axioms hpThetaCNV_squareSubstitution_factor
#print axioms hpThetaPhiWeightedTail_natMoment_integrableOn
#print axioms hpThetaCNV_tailMomentProduct_hasDerivAt
#print axioms hpThetaCNV_tailMomentProduct_derivative_integrableOn
#print axioms hpThetaCNV_tailMomentProduct_tendsto_zero
#print axioms hpThetaPhiWeightedTail_natMoment_eq
#print axioms hpThetaPhiSquareTail_rpowMoment_substitution
#print axioms hpThetaPhiSquareTail_halfMoment_eq_evenMoment
end HodgeProofHP
