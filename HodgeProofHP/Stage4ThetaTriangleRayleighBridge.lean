import HodgeProofHP.Stage4ThetaTriangleSquareMoment
import HodgeProofHP.Stage4ThetaTriangleTestPairing
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
The complex square integral equals the real triangle moment.
The normalized test vector therefore gives a certified operator lower bound.
-/

noncomputable section

namespace HodgeProofHP

open MeasureTheory
open scoped ENNReal

theorem hpThetaTriangle_phi_nonneg_inside
    (u : ℝ) (hu : 0 < u) (hu' : u < 1 / 2) :
    0 ≤ hpRiemannThetaDifferentialKernel u := by
  have hw : 0 < hpThetaTriangleWeight u := by
    unfold hpThetaTriangleWeight
    have hm : 0 < min u (1 / 2 - u) := by
      apply lt_min
      · exact hu
      · linarith
    exact lt_of_lt_of_le hm (le_max_right _ _)
  have h :=
    hpThetaTriangleIntegrand_nonneg u (le_of_lt hu)
  change 0 ≤ hpThetaTriangleWeight u *
    hpRiemannThetaDifferentialKernel u at h
  by_contra hn
  have hn' : hpRiemannThetaDifferentialKernel u < 0 :=
    lt_of_not_ge hn
  have hneg := mul_neg_of_pos_of_neg hw hn'
  linarith

theorem hpThetaTriangle_phi_row_integrable (x : ℝ) :
    IntegrableOn
      (fun y : ℝ => hpRiemannThetaDifferentialKernel (x + y))
      (Set.Ioo (0 : ℝ) (1 / 4)) := by
  have hc :
      Continuous
        (fun y : ℝ => hpRiemannThetaDifferentialKernel (x + y)) :=
    hpRiemannThetaDifferentialKernel_continuous.comp
      (continuous_const.add continuous_id)
  have hi :
      IntegrableOn
        (fun y : ℝ => hpRiemannThetaDifferentialKernel (x + y))
        (Set.Icc (0 : ℝ) (1 / 4)) :=
    hc.continuousOn.integrableOn_Icc
  apply hi.mono_set
  intro y hy
  exact ⟨le_of_lt hy.1, le_of_lt hy.2⟩

theorem hpThetaTriangle_phi_row_nonneg
    (x : ℝ) (hx : x ∈ Set.Ioo (0 : ℝ) (1 / 4)) :
    0 ≤ᵐ[volume.restrict (Set.Ioo (0 : ℝ) (1 / 4))]
      (fun y : ℝ => hpRiemannThetaDifferentialKernel (x + y)) := by
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
  apply hpThetaTriangle_phi_nonneg_inside
  · linarith [hx.1, hy.1]
  · linarith [hx.2, hy.2]

theorem hpThetaTriangle_phi_square_integral_eq_moment :
    (∫ x in Set.Ioo (0 : ℝ) (1 / 4),
      ∫ y in Set.Ioo (0 : ℝ) (1 / 4),
        hpRiemannThetaDifferentialKernel (x + y)) =
      hpThetaTriangleMoment := by
  let g : ℝ → ℝ := fun x =>
    ∫ y in Set.Ioo (0 : ℝ) (1 / 4),
      hpRiemannThetaDifferentialKernel (x + y)
  have hc :
      Continuous
        (fun p : ℝ × ℝ =>
          hpRiemannThetaDifferentialKernel (p.1 + p.2)) :=
    hpRiemannThetaDifferentialKernel_continuous.comp
      (continuous_fst.add continuous_snd)
  have hgsm : StronglyMeasurable g := by
    exact hc.stronglyMeasurable.integral_prod_right'
      (ν := volume.restrict (Set.Ioo (0 : ℝ) (1 / 4)))
  have hgn :
      0 ≤ᵐ[volume.restrict (Set.Ioo (0 : ℝ) (1 / 4))] g := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact integral_nonneg_of_ae
      (hpThetaTriangle_phi_row_nonneg x hx)
  have hrow :
      (fun x => ENNReal.ofReal (g x)) =ᵐ[
        volume.restrict (Set.Ioo (0 : ℝ) (1 / 4))]
      (fun x =>
        ∫⁻ y in Set.Ioo (0 : ℝ) (1 / 4),
          ENNReal.ofReal
            (hpRiemannThetaDifferentialKernel (x + y))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact ofReal_integral_eq_lintegral_ofReal
      (hpThetaTriangle_phi_row_integrable x)
      (hpThetaTriangle_phi_row_nonneg x hx)
  change (∫ x in Set.Ioo (0 : ℝ) (1 / 4), g x) = _
  calc
    (∫ x in Set.Ioo (0 : ℝ) (1 / 4), g x) =
        (∫⁻ x in Set.Ioo (0 : ℝ) (1 / 4),
          ENNReal.ofReal (g x)).toReal :=
      integral_eq_lintegral_of_nonneg_ae hgn
        hgsm.aestronglyMeasurable
    _ = (∫⁻ x in Set.Ioo (0 : ℝ) (1 / 4),
          ∫⁻ y in Set.Ioo (0 : ℝ) (1 / 4),
            ENNReal.ofReal
              (hpRiemannThetaDifferentialKernel (x + y))).toReal := by
      exact congrArg ENNReal.toReal (lintegral_congr_ae hrow)
    _ = hpThetaTriangleMoment :=
      hpThetaTriangle_phi_square_lintegral_toReal

theorem hpThetaTriangle_kernel_square_integral_volume :
    (∫ x in Set.Ioo (0 : ℝ) (1 / 4),
      ∫ y in Set.Ioo (0 : ℝ) (1 / 4),
        hpThetaHankelKernel x y) =
      (hpThetaTriangleMoment : ℂ) := by
  let g : ℝ → ℝ := fun x =>
    ∫ y in Set.Ioo (0 : ℝ) (1 / 4),
      hpRiemannThetaDifferentialKernel (x + y)
  have hrow (x : ℝ) :
      (∫ y in Set.Ioo (0 : ℝ) (1 / 4),
        hpThetaHankelKernel x y) =
      Complex.ofReal (g x) := by
    exact integral_ofReal
      (𝕜 := ℂ)
      (μ := volume.restrict (Set.Ioo (0 : ℝ) (1 / 4)))
      (f := fun y : ℝ =>
        hpRiemannThetaDifferentialKernel (x + y))
  have houter :
      (∫ x in Set.Ioo (0 : ℝ) (1 / 4),
        Complex.ofReal (g x)) =
      Complex.ofReal
        (∫ x in Set.Ioo (0 : ℝ) (1 / 4), g x) := by
    exact integral_ofReal
      (𝕜 := ℂ)
      (μ := volume.restrict (Set.Ioo (0 : ℝ) (1 / 4)))
      (f := g)
  have hreal :
      (∫ x in Set.Ioo (0 : ℝ) (1 / 4), g x) =
      hpThetaTriangleMoment :=
    hpThetaTriangle_phi_square_integral_eq_moment
  calc
    (∫ x in Set.Ioo (0 : ℝ) (1 / 4),
      ∫ y in Set.Ioo (0 : ℝ) (1 / 4),
        hpThetaHankelKernel x y) =
      ∫ x in Set.Ioo (0 : ℝ) (1 / 4),
        Complex.ofReal (g x) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hrow
    _ = Complex.ofReal
        (∫ x in Set.Ioo (0 : ℝ) (1 / 4), g x) := houter
    _ = Complex.ofReal hpThetaTriangleMoment :=
      congrArg Complex.ofReal hreal

theorem hpThetaTriangleTestInterval_restrict_measure :
    hpThetaHankelMeasure.restrict hpThetaTriangleTestInterval =
      volume.restrict (Set.Ioo (0 : ℝ) (1 / 4)) := by
  have hsub :
      hpThetaTriangleTestInterval ⊆ Set.Ioi (0 : ℝ) := by
    intro x hx
    exact hx.1
  unfold hpThetaHankelMeasure
  rw [Measure.restrict_restrict_of_subset hsub]
  rfl

theorem hpThetaTriangleKernelSquareIntegral_eq_moment :
    hpThetaTriangleKernelSquareIntegral =
      (hpThetaTriangleMoment : ℂ) := by
  unfold hpThetaTriangleKernelSquareIntegral
  simp only [hpThetaTriangleTestInterval_restrict_measure]
  exact hpThetaTriangle_kernel_square_integral_volume

theorem hpThetaTriangleTestVector_inner_eq_rayleigh :
    inner ℂ hpThetaTriangleTestVector
      (hpThetaHankelOperator hpThetaTriangleTestVector) =
      (hpThetaHankelTriangleRayleighLower : ℂ) := by
  rw [hpThetaTriangleTestVector_inner_eq_square_integral,
    hpThetaTriangleKernelSquareIntegral_eq_moment]
  unfold hpThetaHankelTriangleRayleighLower
  norm_cast

theorem hpThetaTriangleTestVector_inner_re_eq_rayleigh :
    (inner ℂ hpThetaTriangleTestVector
      (hpThetaHankelOperator hpThetaTriangleTestVector)).re =
      hpThetaHankelTriangleRayleighLower := by
  rw [hpThetaTriangleTestVector_inner_eq_rayleigh]
  simp

theorem hpThetaTriangleTestVector_inner_im_eq_zero :
    (inner ℂ hpThetaTriangleTestVector
      (hpThetaHankelOperator hpThetaTriangleTestVector)).im = 0 := by
  rw [hpThetaTriangleTestVector_inner_eq_rayleigh]
  simp

theorem hpThetaTriangleTestVector_action_norm_gt :
    (117 / 500 : ℝ) <
      ‖hpThetaHankelOperator hpThetaTriangleTestVector‖ := by
  have hle := hpThetaTriangleTestVector_inner_re_le_action_norm
  rw [hpThetaTriangleTestVector_inner_re_eq_rayleigh] at hle
  exact lt_of_lt_of_le hpThetaHankelTriangleRayleighLower_gt hle

theorem hpThetaHankelOperator_norm_gt_triangle_certificate :
    (117 / 500 : ℝ) < ‖hpThetaHankelOperator‖ := by
  exact lt_of_lt_of_le hpThetaTriangleTestVector_action_norm_gt
    hpThetaTriangleTestVector_action_norm_le_opNorm

#print axioms hpThetaTriangle_phi_square_integral_eq_moment
#print axioms hpThetaTriangleKernelSquareIntegral_eq_moment
#print axioms hpThetaTriangleTestVector_inner_eq_rayleigh
#print axioms hpThetaTriangleTestVector_action_norm_gt
#print axioms hpThetaHankelOperator_norm_gt_triangle_certificate

end HodgeProofHP
