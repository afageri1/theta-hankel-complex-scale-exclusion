import HodgeProofHP.Stage4RiemannXiMellinSplit
import Mathlib.Analysis.MellinTransform
import Mathlib.Tactic.Ring

/-!
Inversion of the modified Riemann theta kernel and
the corresponding weighted Mellin inversion identity.
-/

noncomputable section

namespace HodgeProofHP

theorem hpRiemannTheta_g_modif_eq :
    (HurwitzZeta.hurwitzEvenFEPair 0).g_modif =
      hpRiemannModifiedThetaKernel := by
  funext x
  simp [hpRiemannModifiedThetaKernel,
    WeakFEPair.g_modif, WeakFEPair.f_modif,
    HurwitzZeta.hurwitzEvenFEPair, Function.comp_def,
    HurwitzZeta.evenKernel_eq_cosKernel_of_zero]

theorem hpRiemannModifiedThetaKernel_inversion
    (x : ℝ) (hx : 0 < x) :
    hpRiemannModifiedThetaKernel (1 / x) =
      ((x ^ (1 / 2 : ℝ) : ℝ) : ℂ) •
        hpRiemannModifiedThetaKernel x := by
  have h :=
    (HurwitzZeta.hurwitzEvenFEPair 0).hf_modif_FE x hx
  change hpRiemannModifiedThetaKernel (1 / x) =
    (1 * ((x ^ (1 / 2 : ℝ) : ℝ) : ℂ)) •
      (HurwitzZeta.hurwitzEvenFEPair 0).g_modif x at h
  rw [hpRiemannTheta_g_modif_eq] at h
  simpa only [one_mul] using h

theorem hpRiemannModifiedThetaKernel_inversion_above_one
    (x : ℝ) (hx : 1 < x) :
    hpRiemannModifiedThetaKernel (1 / x) =
      ((x ^ (1 / 2 : ℝ) : ℝ) : ℂ) •
        (hpRiemannThetaKernel x : ℂ) := by
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  rw [hpRiemannModifiedThetaKernel_inversion x hx0,
    hpRiemannModifiedThetaKernel_of_one_lt x hx]

theorem hpMellin_weighted_inversion
    (f : ℝ → ℂ) (s a : ℂ) :
    mellin
        (fun x : ℝ => (x⁻¹ : ℂ) ^ a • f x⁻¹) s =
      mellin f (a - s) := by
  calc
    mellin
        (fun x : ℝ => (x⁻¹ : ℂ) ^ a • f x⁻¹) s =
        mellin (fun x : ℝ => (x : ℂ) ^ a • f x) (-s) :=
      by
        simpa using
          (mellin_comp_inv
            (fun x : ℝ => (x : ℂ) ^ a • f x) s)
    _ = mellin f (-s + a) :=
      mellin_cpow_smul f (-s) a
    _ = mellin f (a - s) := by
      congr 1
      ring

end HodgeProofHP

#print axioms HodgeProofHP.hpRiemannTheta_g_modif_eq
#print axioms HodgeProofHP.hpRiemannModifiedThetaKernel_inversion
#print axioms HodgeProofHP.hpRiemannModifiedThetaKernel_inversion_above_one
#print axioms HodgeProofHP.hpMellin_weighted_inversion
