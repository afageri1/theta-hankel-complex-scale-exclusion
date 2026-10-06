import HodgeProofHP.Stage4ModifiedThetaInversion
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
Restricted Mellin inversion and the symmetric upper-half
integral representation of the Riemann xi function.
-/

noncomputable section

open MeasureTheory

namespace HodgeProofHP

def hpModifiedThetaLower : ℝ → ℂ :=
  (Set.Ioo 0 1).indicator hpRiemannModifiedThetaKernel

def hpModifiedThetaUpper : ℝ → ℂ :=
  (Set.Ioi 1).indicator hpRiemannModifiedThetaKernel

theorem hpMellin_indicator_eq_setIntegral
    (f : ℝ → ℂ) (s : ℂ) (S : Set ℝ)
    (hS : MeasurableSet S) (hpos : S ⊆ Set.Ioi 0) :
    mellin (S.indicator f) s =
      ∫ x : ℝ in S, (x : ℂ) ^ (s - 1) • f x := by
  unfold mellin
  have hfun :
      (fun x : ℝ => (x : ℂ) ^ (s - 1) • S.indicator f x) =
        S.indicator (fun x : ℝ => (x : ℂ) ^ (s - 1) • f x) := by
    funext x
    by_cases hx : x ∈ S
    · simp only [Set.indicator_of_mem hx]
    · simp only [Set.indicator_of_notMem hx, smul_zero]
  rw [hfun, setIntegral_indicator hS,
    Set.inter_eq_right.mpr hpos]

theorem hpModifiedThetaLower_inv
    (x : ℝ) (hx0 : 0 < x) :
    hpModifiedThetaLower (1 / x) =
      (x : ℂ) ^ (1 / 2 : ℂ) • hpModifiedThetaUpper x := by
  by_cases hx : 1 < x
  · have hy0 : 0 < 1 / x := one_div_pos.mpr hx0
    have hy1 : 1 / x < 1 :=
      (div_lt_iff₀ hx0).2 (by simpa using hx)
    have hy : 1 / x ∈ Set.Ioo (0 : ℝ) 1 := ⟨hy0, hy1⟩
    have hxmem : x ∈ Set.Ioi (1 : ℝ) := hx
    unfold hpModifiedThetaLower hpModifiedThetaUpper
    rw [Set.indicator_of_mem hy,
      Set.indicator_of_mem hxmem,
      hpRiemannModifiedThetaKernel_inversion x hx0]
    have hpow :
        ((x ^ (1 / 2 : ℝ) : ℝ) : ℂ) =
          (x : ℂ) ^ (1 / 2 : ℂ) := by
      simpa using Complex.ofReal_cpow (le_of_lt hx0) (1 / 2 : ℝ)
    rw [hpow]
  · have hy : 1 / x ∉ Set.Ioo (0 : ℝ) 1 := by
      intro hy
      apply hx
      have h := (div_lt_iff₀ hx0).1 hy.2
      simpa using h
    have hxnot : x ∉ Set.Ioi (1 : ℝ) := hx
    unfold hpModifiedThetaLower hpModifiedThetaUpper
    rw [Set.indicator_of_notMem hy,
      Set.indicator_of_notMem hxnot, smul_zero]

theorem hpModifiedThetaLower_mellin_eq_upper
    (s : ℂ) :
    mellin hpModifiedThetaLower (s / 2) =
      mellin hpModifiedThetaUpper ((1 - s) / 2) := by
  calc
    mellin hpModifiedThetaLower (s / 2) =
        mellin
          (fun x : ℝ => hpModifiedThetaLower x⁻¹)
          (-(s / 2)) := by
      simpa only [neg_neg] using
        (mellin_comp_inv hpModifiedThetaLower (-(s / 2))).symm
    _ = mellin
        (fun x : ℝ =>
          (x : ℂ) ^ (1 / 2 : ℂ) • hpModifiedThetaUpper x)
        (-(s / 2)) := by
      unfold mellin
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      dsimp only
      have hinv :
          hpModifiedThetaLower x⁻¹ =
            (x : ℂ) ^ (1 / 2 : ℂ) • hpModifiedThetaUpper x := by
        simpa only [one_div] using hpModifiedThetaLower_inv x hx
      rw [hinv]
    _ = mellin hpModifiedThetaUpper
        (-(s / 2) + (1 / 2 : ℂ)) :=
      mellin_cpow_smul hpModifiedThetaUpper
        (-(s / 2)) (1 / 2 : ℂ)
    _ = mellin hpModifiedThetaUpper ((1 - s) / 2) := by
      congr 1
      ring

theorem hpModifiedThetaLower_mellin_eq_integral
    (s : ℂ) :
    mellin hpModifiedThetaLower (s / 2) =
      ∫ x : ℝ in Set.Ioo 0 1,
        (x : ℂ) ^ (s / 2 - 1) •
          hpRiemannModifiedThetaKernel x := by
  apply hpMellin_indicator_eq_setIntegral
    hpRiemannModifiedThetaKernel (s / 2)
    (Set.Ioo 0 1) measurableSet_Ioo
  intro x hx
  exact hx.1

theorem hpModifiedThetaUpper_mellin_eq_integral
    (s : ℂ) :
    mellin hpModifiedThetaUpper (s / 2) =
      ∫ x : ℝ in Set.Ioi 1,
        (x : ℂ) ^ (s / 2 - 1) •
          hpRiemannModifiedThetaKernel x := by
  apply hpMellin_indicator_eq_setIntegral
    hpRiemannModifiedThetaKernel (s / 2)
    (Set.Ioi 1) measurableSet_Ioi
  intro x hx
  change (0 : ℝ) < x
  change (1 : ℝ) < x at hx
  linarith

theorem hpRiemannModifiedTheta_lower_integral_eq_upper
    (s : ℂ) :
    (∫ x : ℝ in Set.Ioo 0 1,
      (x : ℂ) ^ (s / 2 - 1) •
        hpRiemannModifiedThetaKernel x) =
    ∫ x : ℝ in Set.Ioi 1,
      (x : ℂ) ^ ((1 - s) / 2 - 1) •
        hpRiemannModifiedThetaKernel x := by
  rw [← hpModifiedThetaLower_mellin_eq_integral s,
    hpModifiedThetaLower_mellin_eq_upper s,
    hpModifiedThetaUpper_mellin_eq_integral (1 - s)]

theorem hpRiemannXi_eq_symmetric_upper_integrals
    (s : ℂ) :
    hpRiemannXi s =
      (s * (s - 1) / 4) *
        ((∫ x : ℝ in Set.Ioi 1,
          (x : ℂ) ^ ((1 - s) / 2 - 1) •
            (hpRiemannThetaKernel x : ℂ)) +
         (∫ x : ℝ in Set.Ioi 1,
          (x : ℂ) ^ (s / 2 - 1) •
            (hpRiemannThetaKernel x : ℂ))) + 1 / 2 := by
  rw [hpRiemannXi_eq_integral,
    hpRiemannModifiedTheta_mellin_integral_split,
    hpRiemannModifiedTheta_lower_integral_eq_upper,
    hpRiemannModifiedTheta_mellin_integral_above_one (1 - s),
    hpRiemannModifiedTheta_mellin_integral_above_one s]

end HodgeProofHP

#print axioms HodgeProofHP.hpMellin_indicator_eq_setIntegral
#print axioms HodgeProofHP.hpModifiedThetaLower_inv
#print axioms HodgeProofHP.hpModifiedThetaLower_mellin_eq_upper
#print axioms HodgeProofHP.hpModifiedThetaLower_mellin_eq_integral
#print axioms HodgeProofHP.hpModifiedThetaUpper_mellin_eq_integral
#print axioms HodgeProofHP.hpRiemannModifiedTheta_lower_integral_eq_upper
#print axioms HodgeProofHP.hpRiemannXi_eq_symmetric_upper_integrals
