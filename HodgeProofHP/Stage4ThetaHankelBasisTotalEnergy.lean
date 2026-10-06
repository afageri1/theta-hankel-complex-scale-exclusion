import HodgeProofHP.Stage4ThetaHankelBasisNormEnergy
import HodgeProofHP.Stage4ThetaFirstTraceObstruction
import Mathlib.MeasureTheory.Integral.Prod

/-!
Identification of basis norm energy with the weighted theta energy.
No operator trace or Fredholm determinant is defined here.
-/

namespace HodgeProofHP

open MeasureTheory

theorem hpThetaHankelRowEnergy_integral_eq_kernel_integral :
    (∫ x, hpThetaHankelRowEnergy x ∂hpThetaHankelMeasure) =
      ∫ p : ℝ × ℝ, ‖hpThetaHankelKernel p.1 p.2‖ ^ 2
        ∂(hpThetaHankelMeasure.prod hpThetaHankelMeasure) := by
  unfold hpThetaHankelRowEnergy
  exact
    (integral_prod
      (fun p : ℝ × ℝ => ‖hpThetaHankelKernel p.1 p.2‖ ^ 2)
      hpThetaHankelKernel_norm_sq_integrable).symm

theorem hpThetaHankelKernel_sq_integral_eq_firstTraceEnergy :
    (∫ p : ℝ × ℝ, ‖hpThetaHankelKernel p.1 p.2‖ ^ 2
      ∂(hpThetaHankelMeasure.prod hpThetaHankelMeasure)) =
      hpThetaFirstTraceEnergy := by
  have hkernel :=
    integral_eq_lintegral_of_nonneg_ae
      (μ := hpThetaHankelMeasure.prod hpThetaHankelMeasure)
      (f := fun p : ℝ × ℝ =>
        ‖hpThetaHankelKernel p.1 p.2‖ ^ 2)
      (Filter.Eventually.of_forall
        (fun p => sq_nonneg ‖hpThetaHankelKernel p.1 p.2‖))
      hpThetaHankelKernel_norm_sq_integrable.aestronglyMeasurable
  have hnonneg :
      0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
        (fun u => u * hpRiemannThetaDifferentialKernel u ^ 2) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact mul_nonneg (le_of_lt hu) (sq_nonneg _)
  have hmeas :
      AEStronglyMeasurable
        (fun u : ℝ => u * hpRiemannThetaDifferentialKernel u ^ 2)
        (volume.restrict (Set.Ioi 0)) :=
    by
      have hc :
          Continuous
            (fun u : ℝ =>
              u * hpRiemannThetaDifferentialKernel u ^ 2) :=
        continuous_id.mul
          (hpRiemannThetaDifferentialKernel_continuous.pow 2)
      exact hc.measurable.aestronglyMeasurable
  have henergy :=
    integral_eq_lintegral_of_nonneg_ae hnonneg hmeas
  have hweight :
      (∫⁻ u : ℝ in Set.Ioi 0,
        ENNReal.ofReal u *
          ENNReal.ofReal (hpRiemannThetaDifferentialKernel u ^ 2)) =
      ∫⁻ u : ℝ in Set.Ioi 0,
        ENNReal.ofReal
          (u * hpRiemannThetaDifferentialKernel u ^ 2) := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact (ENNReal.ofReal_mul (le_of_lt hu)).symm
  calc
    _ = _ := hkernel
    _ = (∫⁻ u : ℝ in Set.Ioi 0,
          ENNReal.ofReal u *
            ENNReal.ofReal
              (hpRiemannThetaDifferentialKernel u ^ 2)).toReal := by
      exact congrArg ENNReal.toReal
        hpThetaHankelKernel_sq_lintegral_weight_identity
    _ = (∫⁻ u : ℝ in Set.Ioi 0,
          ENNReal.ofReal
            (u * hpRiemannThetaDifferentialKernel u ^ 2)).toReal :=
      congrArg ENNReal.toReal hweight
    _ = ∫ u : ℝ in Set.Ioi 0,
          u * hpRiemannThetaDifferentialKernel u ^ 2 :=
      henergy.symm
    _ = hpThetaFirstTraceEnergy := rfl

theorem hpThetaHankelRowEnergy_integral_eq_firstTraceEnergy :
    (∫ x, hpThetaHankelRowEnergy x ∂hpThetaHankelMeasure) =
      hpThetaFirstTraceEnergy := by
  rw [hpThetaHankelRowEnergy_integral_eq_kernel_integral]
  exact hpThetaHankelKernel_sq_integral_eq_firstTraceEnergy

theorem hpThetaHankelBasis_norm_sq_tsum_eq_firstTraceEnergy
    {ι : Type*} [Countable ι]
    (b : HilbertBasis ι ℂ HPThetaHankelSpace) :
    (∑' i, ENNReal.ofReal
      (‖hpThetaHankelOperator (b i)‖ ^ 2)) =
      ENNReal.ofReal hpThetaFirstTraceEnergy := by
  rw [hpThetaHankelBasis_norm_sq_tsum_eq_rowEnergy_integral b,
    hpThetaHankelRowEnergy_integral_eq_firstTraceEnergy]

#print axioms hpThetaHankelRowEnergy_integral_eq_kernel_integral
#print axioms hpThetaHankelKernel_sq_integral_eq_firstTraceEnergy
#print axioms hpThetaHankelRowEnergy_integral_eq_firstTraceEnergy
#print axioms hpThetaHankelBasis_norm_sq_tsum_eq_firstTraceEnergy

end HodgeProofHP
