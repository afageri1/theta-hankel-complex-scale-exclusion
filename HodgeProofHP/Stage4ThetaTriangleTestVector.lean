import HodgeProofHP.Stage4ThetaHankelBoundedOperator
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
The normalized interval indicator used to test the theta Hankel operator.
Its integral representation is proved using almost-everywhere equality.
-/

noncomputable section

namespace HodgeProofHP

open MeasureTheory
open scoped ENNReal

def hpThetaTriangleTestInterval : Set ℝ :=
  Set.Ioo 0 (1 / 4)

theorem hpThetaTriangleTestInterval_measurable :
    MeasurableSet hpThetaTriangleTestInterval :=
  measurableSet_Ioo

theorem hpThetaTriangleTestInterval_measure :
    hpThetaHankelMeasure hpThetaTriangleTestInterval =
      ENNReal.ofReal (1 / 4 : ℝ) := by
  unfold hpThetaHankelMeasure
  rw [Measure.restrict_apply hpThetaTriangleTestInterval_measurable]
  have hsub :
      hpThetaTriangleTestInterval ⊆ Set.Ioi (0 : ℝ) := by
    intro x hx
    exact hx.1
  rw [Set.inter_eq_left.mpr hsub]
  unfold hpThetaTriangleTestInterval
  rw [Real.volume_Ioo]
  norm_num

theorem hpThetaTriangleTestInterval_measure_ne_top :
    hpThetaHankelMeasure hpThetaTriangleTestInterval ≠ ⊤ := by
  rw [hpThetaTriangleTestInterval_measure]
  exact ENNReal.ofReal_ne_top

def hpThetaTriangleTestFunction : ℝ → ℂ :=
  hpThetaTriangleTestInterval.indicator (fun _ => (2 : ℂ))

def hpThetaTriangleTestVector : HPThetaHankelSpace :=
  indicatorConstLp 2 hpThetaTriangleTestInterval_measurable
    hpThetaTriangleTestInterval_measure_ne_top (2 : ℂ)

theorem hpThetaTriangleTestVector_coeFn_ae :
    (fun x => hpThetaTriangleTestVector x)
      =ᵐ[hpThetaHankelMeasure] hpThetaTriangleTestFunction := by
  unfold hpThetaTriangleTestVector hpThetaTriangleTestFunction
  exact indicatorConstLp_coeFn

theorem hpThetaTriangleTestFunction_norm_sq (x : ℝ) :
    ‖hpThetaTriangleTestFunction x‖ ^ 2 =
      hpThetaTriangleTestInterval.indicator
        (fun _ => (4 : ℝ)) x := by
  classical
  by_cases hx : x ∈ hpThetaTriangleTestInterval
  · simp only [hpThetaTriangleTestFunction,
      Set.indicator_of_mem hx]
    norm_num
  · simp only [hpThetaTriangleTestFunction,
      Set.indicator_of_notMem hx, norm_zero]
    norm_num

theorem hpThetaTriangleTestVector_norm_sq :
    ‖hpThetaTriangleTestVector‖ ^ 2 = 1 := by
  rw [hpThetaHankelSpace_norm_sq_eq_integral]
  calc
    (∫ x, ‖hpThetaTriangleTestVector x‖ ^ 2
        ∂hpThetaHankelMeasure) =
        ∫ x, hpThetaTriangleTestInterval.indicator
          (fun _ => (4 : ℝ)) x ∂hpThetaHankelMeasure := by
      apply integral_congr_ae
      filter_upwards [hpThetaTriangleTestVector_coeFn_ae] with x hx
      rw [hx]
      exact hpThetaTriangleTestFunction_norm_sq x
    _ = hpThetaHankelMeasure.real hpThetaTriangleTestInterval *
        (4 : ℝ) := by
      rw [integral_indicator_const (4 : ℝ)
        hpThetaTriangleTestInterval_measurable]
      rfl
    _ = 1 := by
      unfold Measure.real
      rw [hpThetaTriangleTestInterval_measure]
      norm_num

theorem hpThetaTriangleTestVector_norm :
    ‖hpThetaTriangleTestVector‖ = 1 := by
  have h := hpThetaTriangleTestVector_norm_sq
  nlinarith [norm_nonneg hpThetaTriangleTestVector]

theorem hpThetaTriangleTestVector_ne_zero :
    hpThetaTriangleTestVector ≠ 0 := by
  intro h
  have hn := hpThetaTriangleTestVector_norm
  rw [h, norm_zero] at hn
  norm_num at hn

theorem hpThetaTriangleTestVector_action (x : ℝ) :
    hpThetaHankelActionFunction hpThetaTriangleTestVector x =
      (2 : ℂ) *
        ∫ y in hpThetaTriangleTestInterval,
          hpThetaHankelKernel x y ∂hpThetaHankelMeasure := by
  classical
  unfold hpThetaHankelActionFunction
  calc
    (∫ y, hpThetaHankelKernel x y * hpThetaTriangleTestVector y
        ∂hpThetaHankelMeasure) =
        ∫ y, hpThetaTriangleTestInterval.indicator
          (fun y => hpThetaHankelKernel x y * (2 : ℂ)) y
            ∂hpThetaHankelMeasure := by
      apply integral_congr_ae
      filter_upwards [hpThetaTriangleTestVector_coeFn_ae] with y hy
      rw [hy]
      by_cases hmem : y ∈ hpThetaTriangleTestInterval
      · simp only [hpThetaTriangleTestFunction,
          Set.indicator_of_mem hmem]
      · simp only [hpThetaTriangleTestFunction,
          Set.indicator_of_notMem hmem, mul_zero]
    _ = ∫ y in hpThetaTriangleTestInterval,
        hpThetaHankelKernel x y * (2 : ℂ)
          ∂hpThetaHankelMeasure := by
      rw [integral_indicator hpThetaTriangleTestInterval_measurable]
    _ = (2 : ℂ) *
        ∫ y in hpThetaTriangleTestInterval,
          hpThetaHankelKernel x y ∂hpThetaHankelMeasure := by
      rw [integral_mul_const]
      ring

theorem hpThetaTriangleTestVector_operator_coeFn_ae :
    (fun x => hpThetaHankelOperator hpThetaTriangleTestVector x)
      =ᵐ[hpThetaHankelMeasure]
    (fun x => (2 : ℂ) *
      ∫ y in hpThetaTriangleTestInterval,
        hpThetaHankelKernel x y ∂hpThetaHankelMeasure) := by
  filter_upwards
    [hpThetaHankelOperator_coeFn_ae hpThetaTriangleTestVector]
    with x hx
  rw [hx]
  exact hpThetaTriangleTestVector_action x

#print axioms hpThetaTriangleTestVector_norm
#print axioms hpThetaTriangleTestVector_action
#print axioms hpThetaTriangleTestVector_operator_coeFn_ae

end HodgeProofHP
