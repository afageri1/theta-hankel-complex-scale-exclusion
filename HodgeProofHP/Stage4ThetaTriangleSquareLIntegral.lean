import HodgeProofHP.Stage4ThetaHankelTranslation
import HodgeProofHP.Stage4ThetaTriangleLowerCertificate

/-!
Translation and Tonelli identify the integral over the quarter-side square
with the triangularly weighted integral on the positive half-line.
-/

noncomputable section

namespace HodgeProofHP

open MeasureTheory
open scoped ENNReal

theorem hpThetaTriangle_lintegral_translate
    (F : ℝ → ℝ≥0∞) (hF : Measurable F) (x : ℝ) :
    (∫⁻ y in Set.Ioo (0 : ℝ) (1 / 4), F (x + y)) =
      ∫⁻ u in Set.Ioo x (x + 1 / 4), F u := by
  have hpre :
      (fun y : ℝ => x + y) ⁻¹' Set.Ioo x (x + 1 / 4) =
        Set.Ioo (0 : ℝ) (1 / 4) := by
    ext y
    simp only [Set.mem_preimage, Set.mem_Ioo]
    constructor
    · rintro ⟨h₁, h₂⟩
      constructor <;> linarith
    · rintro ⟨h₁, h₂⟩
      constructor <;> linarith
  have h :=
    (measurePreserving_add_left (volume : Measure ℝ) x).setLIntegral_comp_preimage
        (s := Set.Ioo x (x + 1 / 4)) measurableSet_Ioo hF
  simpa only [hpre] using h

theorem hpThetaTriangle_fiber_length (u : ℝ) :
    ENNReal.ofReal
        (min (1 / 4 : ℝ) u - max 0 (u - 1 / 4)) =
      ENNReal.ofReal (hpThetaTriangleWeight u) := by
  unfold hpThetaTriangleWeight
  by_cases h₀ : u ≤ 0
  · have h₁ : u ≤ (1 / 4 : ℝ) := by linarith
    have h₂ : u - 1 / 4 ≤ 0 := by linarith
    have h₃ : u ≤ 1 / 2 - u := by linarith
    rw [min_eq_right h₁, max_eq_left h₂, sub_zero,
      min_eq_left h₃, max_eq_left h₀]
    simp [ENNReal.ofReal_of_nonpos h₀]
  · have hu : 0 ≤ u := le_of_lt (lt_of_not_ge h₀)
    by_cases h₁ : u ≤ (1 / 4 : ℝ)
    · have h₂ : u - 1 / 4 ≤ 0 := by linarith
      have h₃ : u ≤ 1 / 2 - u := by linarith
      rw [min_eq_right h₁, max_eq_left h₂, sub_zero,
        min_eq_left h₃, max_eq_right hu]
    · have ha : (1 / 4 : ℝ) ≤ u := by linarith
      have h₂ : 0 ≤ u - 1 / 4 := by linarith
      have h₃ : 1 / 2 - u ≤ u := by linarith
      rw [min_eq_left ha, max_eq_right h₂, min_eq_right h₃]
      by_cases h₄ : u ≤ (1 / 2 : ℝ)
      · have h₅ : 0 ≤ 1 / 2 - u := by linarith
        rw [max_eq_right h₅]
        congr 1
        ring
      · have h₅ : 1 / 2 - u ≤ 0 := by linarith
        have h₆ : (1 / 4 : ℝ) - (u - 1 / 4) ≤ 0 := by
          linarith
        rw [max_eq_left h₅,
          ENNReal.ofReal_of_nonpos h₆]
        simp

theorem hpThetaTriangle_square_lintegral
    (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ x in Set.Ioo (0 : ℝ) (1 / 4),
      ∫⁻ y in Set.Ioo (0 : ℝ) (1 / 4), F (x + y)) =
      ∫⁻ u in Set.Ioi (0 : ℝ),
        ENNReal.ofReal (hpThetaTriangleWeight u) * F u := by
  classical
  have hG :
      Measurable
        (fun p : ℝ × ℝ =>
          (Set.Ioo p.1 (p.1 + 1 / 4)).indicator F p.2) := by
    have heq :
        (fun p : ℝ × ℝ =>
          (Set.Ioo p.1 (p.1 + 1 / 4)).indicator F p.2) =
        ({p : ℝ × ℝ |
          p.1 < p.2 ∧ p.2 < p.1 + 1 / 4}).indicator
          (fun p => F p.2) := by
      funext p
      rfl
    rw [heq]
    exact (hF.comp measurable_snd).indicator
      ((measurableSet_lt measurable_fst measurable_snd).inter
        (measurableSet_lt measurable_snd
          (measurable_fst.add measurable_const)))

  have hswap :
      (∫⁻ x in Set.Ioo (0 : ℝ) (1 / 4),
        ∫⁻ u, (Set.Ioo x (x + 1 / 4)).indicator F u) =
      ∫⁻ u, ∫⁻ x in Set.Ioo (0 : ℝ) (1 / 4),
        (Set.Ioo x (x + 1 / 4)).indicator F u := by
    exact lintegral_lintegral_swap hG.aemeasurable

  have hinner (u : ℝ) :
      (∫⁻ x in Set.Ioo (0 : ℝ) (1 / 4),
        (Set.Ioo x (x + 1 / 4)).indicator F u) =
      ENNReal.ofReal (hpThetaTriangleWeight u) * F u := by
    have heq :
        (fun x : ℝ => (Set.Ioo x (x + 1 / 4)).indicator F u) =
        (Set.Ioo (u - 1 / 4) u).indicator
          (fun _x : ℝ => F u) := by
      funext x
      have hmem :
          u ∈ Set.Ioo x (x + 1 / 4) ↔
            x ∈ Set.Ioo (u - 1 / 4) u := by
        simp only [Set.mem_Ioo]
        constructor
        · rintro ⟨h₁, h₂⟩
          constructor <;> linarith
        · rintro ⟨h₁, h₂⟩
          constructor <;> linarith
      simp only [Set.indicator_apply, hmem]
    rw [heq, setLIntegral_indicator measurableSet_Ioo]
    have hset :
        Set.Ioo (u - 1 / 4) u ∩ Set.Ioo (0 : ℝ) (1 / 4) =
        Set.Ioo (max 0 (u - 1 / 4)) (min (1 / 4) u) := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Ioo,
        max_lt_iff, lt_min_iff]
      tauto
    rw [hset, setLIntegral_const, Real.volume_Ioo, mul_comm,
      hpThetaTriangle_fiber_length]

  have hsupport :
      (fun u : ℝ =>
        ENNReal.ofReal (hpThetaTriangleWeight u) * F u) =
      (Set.Ioi (0 : ℝ)).indicator
        (fun u : ℝ =>
          ENNReal.ofReal (hpThetaTriangleWeight u) * F u) := by
    funext u
    by_cases hu : u ∈ Set.Ioi (0 : ℝ)
    · simp only [Set.indicator_of_mem hu]
    · have h₀ : u ≤ 0 := by
        simpa only [Set.mem_Ioi, not_lt] using hu
      have h₁ : u ≤ 1 / 2 - u := by linarith
      have hw : hpThetaTriangleWeight u = 0 := by
        unfold hpThetaTriangleWeight
        rw [min_eq_left h₁, max_eq_left h₀]
      simp [Set.indicator_of_notMem hu, hw]

  calc
    (∫⁻ x in Set.Ioo (0 : ℝ) (1 / 4),
      ∫⁻ y in Set.Ioo (0 : ℝ) (1 / 4), F (x + y)) =
        ∫⁻ x in Set.Ioo (0 : ℝ) (1 / 4),
          ∫⁻ u in Set.Ioo x (x + 1 / 4), F u := by
      simp_rw [hpThetaTriangle_lintegral_translate F hF]
    _ = ∫⁻ x in Set.Ioo (0 : ℝ) (1 / 4),
          ∫⁻ u, (Set.Ioo x (x + 1 / 4)).indicator F u := by
      simp_rw [lintegral_indicator measurableSet_Ioo]
    _ = ∫⁻ u, ∫⁻ x in Set.Ioo (0 : ℝ) (1 / 4),
          (Set.Ioo x (x + 1 / 4)).indicator F u := hswap
    _ = ∫⁻ u,
          ENNReal.ofReal (hpThetaTriangleWeight u) * F u := by
      simp_rw [hinner]
    _ = ∫⁻ u in Set.Ioi (0 : ℝ),
          ENNReal.ofReal (hpThetaTriangleWeight u) * F u := by
      calc
        _ = ∫⁻ u : ℝ,
            (Set.Ioi (0 : ℝ)).indicator
              (fun u : ℝ =>
                ENNReal.ofReal (hpThetaTriangleWeight u) * F u) u :=
          congrArg (fun f : ℝ → ℝ≥0∞ => ∫⁻ u, f u) hsupport
        _ = _ :=
          lintegral_indicator
            (μ := (volume : Measure ℝ))
            measurableSet_Ioi _

theorem hpThetaTriangle_phi_square_lintegral :
    (∫⁻ x in Set.Ioo (0 : ℝ) (1 / 4),
      ∫⁻ y in Set.Ioo (0 : ℝ) (1 / 4),
        ENNReal.ofReal (hpRiemannThetaDifferentialKernel (x + y))) =
      ∫⁻ u in Set.Ioi (0 : ℝ),
        ENNReal.ofReal (hpThetaTriangleWeight u) *
          ENNReal.ofReal (hpRiemannThetaDifferentialKernel u) := by
  exact hpThetaTriangle_square_lintegral
    (fun u => ENNReal.ofReal (hpRiemannThetaDifferentialKernel u))
    hpRiemannThetaDifferentialKernel_continuous.measurable.ennreal_ofReal

#print axioms hpThetaTriangle_square_lintegral
#print axioms hpThetaTriangle_phi_square_lintegral

end HodgeProofHP
