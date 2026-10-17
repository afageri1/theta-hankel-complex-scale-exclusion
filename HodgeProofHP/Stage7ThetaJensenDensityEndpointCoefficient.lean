/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenDensityCurvatureBoundary
import HodgeProofHP.Stage7ThetaJensenKernelFourthDerivativeMajorant

/-!
# Higher-order density endpoint coefficient

Reflection forces the third kernel derivative to vanish at zero.
The actual derivative limits give L'(t)/t^2 -> D from the right,
where D = 3 Phi''(0)^2 - Phi(0) Phi''''(0).
If D > 0, a mean-value argument yields L(t) >= (D/6) t^3
on some right interval. No numerical sign certificate for D is asserted.
-/

noncomputable section
open Set Filter
open scoped Topology
namespace HodgeProofHP

private theorem hpDensityEndpoint_d0 (t : ℝ) :
    HasDerivAt hpRiemannThetaDifferentialKernel
      (deriv hpRiemannThetaDifferentialKernel t) t := by
  rw [hpThetaPhi_deriv_eq_kernelSeries]
  exact hpThetaPhi_hasDerivAt_kernelSeries t

private theorem hpDensityEndpoint_d1 (t : ℝ) :
    HasDerivAt (deriv hpRiemannThetaDifferentialKernel)
      (deriv (deriv hpRiemannThetaDifferentialKernel) t) t := by
  rw [hpThetaPhi_secondDeriv_eq_kernelSeries]
  exact hpThetaPhi_deriv_hasDerivAt_kernelSeries t

private theorem hpDensityEndpoint_d2 (t : ℝ) :
    HasDerivAt (deriv (deriv hpRiemannThetaDifferentialKernel))
      (deriv (deriv (deriv hpRiemannThetaDifferentialKernel)) t) t := by
  rw [hpThetaPhi_thirdDeriv_eq_kernelSeries]
  exact hpThetaPhi_secondDeriv_hasDerivAt_kernelSeries t

private theorem hpDensityEndpoint_d3 (t : ℝ) :
    HasDerivAt (deriv (deriv (deriv hpRiemannThetaDifferentialKernel)))
      (deriv (deriv (deriv (deriv hpRiemannThetaDifferentialKernel))) t) t := by
  rw [hpThetaPhi_fourthDeriv_eq_kernelSeries]
  exact hpThetaPhi_thirdDeriv_hasDerivAt_kernelSeries t

theorem hpThetaPhi_density_first_reflection (t : ℝ) :
    -deriv hpRiemannThetaDifferentialKernel (-t) =
      deriv hpRiemannThetaDifferentialKernel t := by
  have hneg : HasDerivAt (fun v : ℝ => -v) (-1 : ℝ) t := by
    simpa only [id_eq] using (hasDerivAt_id t).neg
  have hn : HasDerivAt (fun v : ℝ => hpRiemannThetaDifferentialKernel (-v))
      (-deriv hpRiemannThetaDifferentialKernel (-t)) t := by
    simpa only [Function.comp_def, mul_neg, mul_one] using
      (hpDensityEndpoint_d0 (-t)).comp t hneg
  have he : (fun v : ℝ => hpRiemannThetaDifferentialKernel (-v)) =
      hpRiemannThetaDifferentialKernel := funext hpThetaPhi_reflection
  rw [he] at hn
  exact hn.unique (hpDensityEndpoint_d0 t)

theorem hpThetaPhi_density_second_reflection (t : ℝ) :
    deriv (deriv hpRiemannThetaDifferentialKernel) (-t) =
      deriv (deriv hpRiemannThetaDifferentialKernel) t := by
  have hneg : HasDerivAt (fun v : ℝ => -v) (-1 : ℝ) t := by
    simpa only [id_eq] using (hasDerivAt_id t).neg
  have hn : HasDerivAt (fun v : ℝ => -deriv hpRiemannThetaDifferentialKernel (-v))
      (deriv (deriv hpRiemannThetaDifferentialKernel) (-t)) t := by
    simpa only [Function.comp_def, mul_neg, mul_one, neg_neg] using
      ((hpDensityEndpoint_d1 (-t)).comp t hneg).neg
  have he : (fun v : ℝ => -deriv hpRiemannThetaDifferentialKernel (-v)) =
      deriv hpRiemannThetaDifferentialKernel := funext hpThetaPhi_density_first_reflection
  rw [he] at hn
  exact hn.unique (hpDensityEndpoint_d1 t)

theorem hpThetaPhi_thirdDeriv_zero :
    deriv (deriv (deriv hpRiemannThetaDifferentialKernel)) 0 = 0 := by
  have hneg : HasDerivAt (fun v : ℝ => -v) (-1 : ℝ) 0 := by
    simpa only [id_eq] using (hasDerivAt_id (0 : ℝ)).neg
  have hn : HasDerivAt
      (fun v : ℝ => deriv (deriv hpRiemannThetaDifferentialKernel) (-v))
      (-deriv (deriv (deriv hpRiemannThetaDifferentialKernel)) 0) 0 := by
    simpa only [Function.comp_def, neg_zero, mul_neg, mul_one] using
      (hpDensityEndpoint_d2 (-(0 : ℝ))).comp 0 hneg
  have he : (fun v : ℝ => deriv (deriv hpRiemannThetaDifferentialKernel) (-v)) =
      deriv (deriv hpRiemannThetaDifferentialKernel) :=
    funext hpThetaPhi_density_second_reflection
  rw [he] at hn
  have h := hn.unique (hpDensityEndpoint_d2 0)
  linarith

theorem hpThetaPhi_deriv_div_tendsto_right :
    Tendsto (fun t : ℝ => deriv hpRiemannThetaDifferentialKernel t / t)
      (𝓝[>] (0 : ℝ)) (𝓝 (deriv (deriv hpRiemannThetaDifferentialKernel) 0)) := by
  have hr := (hpDensityEndpoint_d1 0).hasDerivWithinAt (s := Set.Ioi 0)
  have h := (hasDerivWithinAt_iff_tendsto_slope'
    (show (0 : ℝ) ∉ Set.Ioi 0 by simp)).mp hr
  have he : slope (deriv hpRiemannThetaDifferentialKernel) 0 =
      (fun t : ℝ => deriv hpRiemannThetaDifferentialKernel t / t) := by
    funext t
    simp only [slope_def_field, hpThetaPhi_deriv_zero, sub_zero]
  rw [he] at h
  exact h

theorem hpThetaPhi_thirdDeriv_div_tendsto_right :
    Tendsto (fun t : ℝ =>
      deriv (deriv (deriv hpRiemannThetaDifferentialKernel)) t / t)
      (𝓝[>] (0 : ℝ))
      (𝓝 (deriv (deriv (deriv (deriv hpRiemannThetaDifferentialKernel))) 0)) := by
  have hr := (hpDensityEndpoint_d3 0).hasDerivWithinAt (s := Set.Ioi 0)
  have h := (hasDerivWithinAt_iff_tendsto_slope'
    (show (0 : ℝ) ∉ Set.Ioi 0 by simp)).mp hr
  have he : slope (deriv (deriv (deriv hpRiemannThetaDifferentialKernel))) 0 =
      (fun t : ℝ => deriv (deriv (deriv hpRiemannThetaDifferentialKernel)) t / t) := by
    funext t
    simp only [slope_def_field, hpThetaPhi_thirdDeriv_zero, sub_zero]
  rw [he] at h
  exact h

def hpThetaPhiDensityEndpointCoefficient : ℝ :=
  3 * deriv (deriv hpRiemannThetaDifferentialKernel) 0 ^ 2 -
    hpRiemannThetaDifferentialKernel 0 *
      deriv (deriv (deriv (deriv hpRiemannThetaDifferentialKernel))) 0

theorem hpThetaPhiDensityCurvatureFirstDerivative_div_sq (t : ℝ) (ht : t ≠ 0) :
    hpThetaPhiDensityCurvatureFirstDerivative t / t ^ 2 =
      2 * (deriv hpRiemannThetaDifferentialKernel t / t) ^ 2 +
      (deriv hpRiemannThetaDifferentialKernel t / t) *
        deriv (deriv hpRiemannThetaDifferentialKernel) t -
      hpRiemannThetaDifferentialKernel t *
        (deriv (deriv (deriv hpRiemannThetaDifferentialKernel)) t / t) := by
  unfold hpThetaPhiDensityCurvatureFirstDerivative
  field_simp [ht] <;> ring

theorem hpThetaPhiDensityCurvatureFirstDerivative_div_sq_tendsto_right :
    Tendsto (fun t : ℝ => hpThetaPhiDensityCurvatureFirstDerivative t / t ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 hpThetaPhiDensityEndpointCoefficient) := by
  have hphi : Tendsto hpRiemannThetaDifferentialKernel (𝓝[>] (0 : ℝ))
      (𝓝 (hpRiemannThetaDifferentialKernel 0)) :=
    (hpDensityEndpoint_d0 0).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hphi2 : Tendsto (deriv (deriv hpRiemannThetaDifferentialKernel))
      (𝓝[>] (0 : ℝ)) (𝓝 (deriv (deriv hpRiemannThetaDifferentialKernel) 0)) :=
    (hpDensityEndpoint_d2 0).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have h1 := hpThetaPhi_deriv_div_tendsto_right
  have h3 := hpThetaPhi_thirdDeriv_div_tendsto_right
  have hlim := (((h1.pow 2).const_mul 2).add (h1.mul hphi2)).sub (hphi.mul h3)
  have hcoef :
      2 * deriv (deriv hpRiemannThetaDifferentialKernel) 0 ^ 2 +
        deriv (deriv hpRiemannThetaDifferentialKernel) 0 *
          deriv (deriv hpRiemannThetaDifferentialKernel) 0 -
        hpRiemannThetaDifferentialKernel 0 *
          deriv (deriv (deriv (deriv hpRiemannThetaDifferentialKernel))) 0 =
      hpThetaPhiDensityEndpointCoefficient := by
    unfold hpThetaPhiDensityEndpointCoefficient
    ring
  rw [hcoef] at hlim
  apply (tendsto_congr' ?_).mpr hlim
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact hpThetaPhiDensityCurvatureFirstDerivative_div_sq t (ne_of_gt ht)

theorem hpThetaPhiDensityCurvature_exists_cubic_lower_of_coefficient_pos
    (hD : 0 < hpThetaPhiDensityEndpointCoefficient) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ →
      hpThetaPhiDensityEndpointCoefficient / 6 * t ^ 3 ≤ hpThetaPhiDensityCurvature t := by
  let D := hpThetaPhiDensityEndpointCoefficient
  have hevent : {t : ℝ | D / 2 <
      hpThetaPhiDensityCurvatureFirstDerivative t / t ^ 2} ∈ 𝓝[>] (0 : ℝ) :=
    hpThetaPhiDensityCurvatureFirstDerivative_div_sq_tendsto_right.eventually
      (Ioi_mem_nhds (by dsimp [D]; linarith))
  rcases Metric.mem_nhdsWithin_iff.mp hevent with ⟨δ, hδ, hsub⟩
  refine ⟨δ, hδ, ?_⟩
  intro t ht htδ
  let H : ℝ → ℝ := fun u => hpThetaPhiDensityCurvature u - D / 6 * u ^ 3
  have hH (u : ℝ) : HasDerivAt H
      (hpThetaPhiDensityCurvatureFirstDerivative u - D / 2 * u ^ 2) u := by
    have h := (hpThetaPhiDensityCurvature_hasDerivAt u).sub
      (((hasDerivAt_id u).pow 3).const_mul (D / 6))
    change HasDerivAt H _ u at h
    convert h using 1 <;> norm_num [id_eq] <;> ring
  have hc : ContinuousOn H (Set.Icc 0 t) := by
    intro u hu
    exact (hH u).continuousAt.continuousWithinAt
  have hd : DifferentiableOn ℝ H (interior (Set.Icc 0 t)) := by
    intro u hu
    exact (hH u).differentiableAt.differentiableWithinAt
  have hb : ∀ u ∈ interior (Set.Icc 0 t), (0 : ℝ) ≤ deriv H u := by
    intro u hu
    have hu' : u ∈ Set.Ioo 0 t := by simpa only [interior_Icc] using hu
    have hupper : D / 2 < hpThetaPhiDensityCurvatureFirstDerivative u / u ^ 2 := by
      apply hsub
      constructor
      · simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hu'.1] using
          hu'.2.trans htδ
      · exact hu'.1
    have hbound := (lt_div_iff₀ (sq_pos_of_pos hu'.1)).mp hupper
    rw [(hH u).deriv]
    linarith
  have h := (convex_Icc (0 : ℝ) t).mul_sub_le_image_sub_of_le_deriv
    hc hd hb 0 ⟨le_rfl, ht.le⟩ t ⟨ht.le, le_rfl⟩ ht.le
  dsimp [H] at h
  simp only [hpThetaPhiDensityCurvature_zero, zero_pow (by norm_num : (3 : ℕ) ≠ 0),
    mul_zero, sub_zero, zero_mul] at h
  dsimp [D] at h
  linarith

#print axioms hpThetaPhi_density_first_reflection
#print axioms hpThetaPhi_density_second_reflection
#print axioms hpThetaPhi_thirdDeriv_zero
#print axioms hpThetaPhi_deriv_div_tendsto_right
#print axioms hpThetaPhi_thirdDeriv_div_tendsto_right
#print axioms hpThetaPhiDensityCurvatureFirstDerivative_div_sq
#print axioms hpThetaPhiDensityCurvatureFirstDerivative_div_sq_tendsto_right
#print axioms hpThetaPhiDensityCurvature_exists_cubic_lower_of_coefficient_pos
end HodgeProofHP
