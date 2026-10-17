/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenCNVGammaNormalization

/-!
# Strict integral comparison on the positive half-line

A strictly increasing score has strictly positive covariance with x under
any everywhere positive weight whose four required integrals exist. The
proof centers at the weighted mean, and uses no double-integral interchange.
The actual score -K'/K is strictly increasing by the certified CNV curvature.

Application to the half-integer moment weights still requires the two
score-weighted integrability identities. No normalized moment inequality,
general Turan inequality, or unbounded good-degree theorem is asserted here.
-/
noncomputable section
open MeasureTheory Filter
namespace HodgeProofHP

theorem hpThetaCNV_integral_pos_of_pos_on_Ioi (f : ℝ → ℝ)
    (hf : IntegrableOn f (Set.Ioi 0) volume) (hpos : ∀ x, 0 < x → 0 < f x) :
    0 < ∫ x in Set.Ioi (0 : ℝ), f x := by
  have hs : Function.support f ∩ Set.Ioi 0 = Set.Ioi 0 := by
    rw [Set.inter_eq_right]
    intro x hx
    exact (hpos x hx).ne'
  rw [setIntegral_pos_iff_support_of_nonneg_ae]
  · rw [hs, Real.volume_Ioi, ← ENNReal.ofReal_zero]
    exact ENNReal.ofReal_lt_top
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact (hpos x hx).le
  · exact hf

theorem hpThetaCNV_strict_integral_comparison (w q : ℝ → ℝ)
    (hw : IntegrableOn w (Set.Ioi 0) volume)
    (hxw : IntegrableOn (fun x => x * w x) (Set.Ioi 0) volume)
    (hqw : IntegrableOn (fun x => q x * w x) (Set.Ioi 0) volume)
    (hxqw : IntegrableOn (fun x => x * q x * w x) (Set.Ioi 0) volume)
    (hwpos : ∀ x, 0 < x → 0 < w x)
    (hq : StrictMonoOn q (Set.Ioi (0 : ℝ))) :
    (∫ x in Set.Ioi (0 : ℝ), x * w x) * (∫ x in Set.Ioi (0 : ℝ), q x * w x) <
      (∫ x in Set.Ioi (0 : ℝ), w x) * (∫ x in Set.Ioi (0 : ℝ), x * q x * w x) := by
  let A : ℝ := ∫ x in Set.Ioi (0 : ℝ), w x
  let B : ℝ := ∫ x in Set.Ioi (0 : ℝ), x * w x
  let C : ℝ := ∫ x in Set.Ioi (0 : ℝ), q x * w x
  let D : ℝ := ∫ x in Set.Ioi (0 : ℝ), x * q x * w x
  have hA : 0 < A := hpThetaCNV_integral_pos_of_pos_on_Ioi w hw hwpos
  have hB : 0 < B := hpThetaCNV_integral_pos_of_pos_on_Ioi _ hxw
    (fun x hx => mul_pos hx (hwpos x hx))
  let c : ℝ := B / A
  have hc : 0 < c := div_pos hB hA
  have hmean : c * A = B := div_mul_cancel₀ B hA.ne'
  let f : ℝ → ℝ := fun x => x * q x * w x - c * (q x * w x) -
    q c * (x * w x) + (c * q c) * w x
  have hf : IntegrableOn f (Set.Ioi 0) volume :=
    ((hxqw.sub (hqw.const_mul c)).sub (hxw.const_mul (q c))).add
      (hw.const_mul (c * q c))
  have hfactor (x : ℝ) : f x = (x - c) * (q x - q c) * w x := by
    dsimp [f]
    ring
  have hnonneg : ∀ x, 0 < x → 0 ≤ f x := by
    intro x hx
    rw [hfactor]
    rcases lt_trichotomy x c with hxc | rfl | hcx
    · exact (mul_pos (mul_pos_of_neg_of_neg (sub_neg.mpr hxc)
        (sub_neg.mpr (hq hx hc hxc))) (hwpos x hx)).le
    · simp
    · exact (mul_pos (mul_pos (sub_pos.mpr hcx)
        (sub_pos.mpr (hq hc hx hcx))) (hwpos x hx)).le
  have hsupport : Set.Ioi (c + 1) ⊆ Function.support f ∩ Set.Ioi 0 := by
    intro x hx
    have hcx : c < x := by linarith
    have hx0 : 0 < x := hc.trans hcx
    refine ⟨?_, hx0⟩
    rw [Function.mem_support, hfactor]
    exact (mul_pos (mul_pos (sub_pos.mpr hcx)
      (sub_pos.mpr (hq hc hx0 hcx))) (hwpos x hx0)).ne'
  have hpositive : 0 < ∫ x in Set.Ioi (0 : ℝ), f x := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae]
    · have hm : volume (Set.Ioi (c + 1)) ≤ volume (Function.support f ∩ Set.Ioi 0) :=
        measure_mono hsupport
      rw [Real.volume_Ioi] at hm
      exact lt_of_lt_of_le (by simp : (0 : ℝ≥0∞) < ⊤) hm
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact hnonneg x hx
    · exact hf
  have heval : (∫ x in Set.Ioi (0 : ℝ), f x) = D - c * C - q c * B + (c * q c) * A := by
    dsimp [f, A, B, C, D]
    rw [integral_add ((hxqw.sub (hqw.const_mul c)).sub (hxw.const_mul (q c)))
      (hw.const_mul (c * q c)),
      integral_sub (hxqw.sub (hqw.const_mul c)) (hxw.const_mul (q c)),
      integral_sub hxqw (hqw.const_mul c)]
    simp only [integral_const_mul]
  have heval' : (∫ x in Set.Ioi (0 : ℝ), f x) = D - c * C := by
    rw [heval]
    have hm := congrArg (fun z : ℝ => q c * z) hmean
    nlinarith [hm]
  have hp := mul_pos hA hpositive
  rw [heval'] at hp
  have hm := congrArg (fun z : ℝ => z * C) hmean
  change B * C < A * D
  nlinarith [hm, hp]

def hpThetaCNVScore (x : ℝ) : ℝ := -hpThetaPhiSquareTailLogSlope x

theorem hpThetaCNVScore_eq_kernel_ratio (x : ℝ) :
    hpThetaCNVScore x =
      hpRiemannThetaDifferentialKernel (Real.sqrt x) / hpThetaPhiSquareTail x := by
  unfold hpThetaCNVScore hpThetaPhiSquareTailLogSlope
  ring

theorem hpThetaCNVScore_pos (x : ℝ) (hx : 0 < x) : 0 < hpThetaCNVScore x := by
  rw [hpThetaCNVScore_eq_kernel_ratio]
  exact div_pos (hpThetaPhi_pos_on_nonnegative _ (Real.sqrt_nonneg x))
    (hpThetaPhiSquareTail_pos x hx)

theorem hpThetaCNVScore_strictMonoOn :
    StrictMonoOn hpThetaCNVScore (Set.Ioi (0 : ℝ)) := by
  intro x hx y hy hxy
  exact neg_lt_neg (hpThetaPhiSquareTailLogSlope_strictAntiOn hx hy hxy)

theorem hpThetaCNVScore_weighted_integral_comparison (w : ℝ → ℝ)
    (hw : IntegrableOn w (Set.Ioi 0) volume)
    (hxw : IntegrableOn (fun x => x * w x) (Set.Ioi 0) volume)
    (hqw : IntegrableOn (fun x => hpThetaCNVScore x * w x) (Set.Ioi 0) volume)
    (hxqw : IntegrableOn (fun x => x * hpThetaCNVScore x * w x) (Set.Ioi 0) volume)
    (hwpos : ∀ x, 0 < x → 0 < w x) :
    (∫ x in Set.Ioi (0 : ℝ), x * w x) *
        (∫ x in Set.Ioi (0 : ℝ), hpThetaCNVScore x * w x) <
      (∫ x in Set.Ioi (0 : ℝ), w x) *
        (∫ x in Set.Ioi (0 : ℝ), x * hpThetaCNVScore x * w x) :=
  hpThetaCNV_strict_integral_comparison w hpThetaCNVScore hw hxw hqw hxqw hwpos
    hpThetaCNVScore_strictMonoOn

#print axioms hpThetaCNV_integral_pos_of_pos_on_Ioi
#print axioms hpThetaCNV_strict_integral_comparison
#print axioms hpThetaCNVScore_eq_kernel_ratio
#print axioms hpThetaCNVScore_pos
#print axioms hpThetaCNVScore_strictMonoOn
#print axioms hpThetaCNVScore_weighted_integral_comparison
end HodgeProofHP
