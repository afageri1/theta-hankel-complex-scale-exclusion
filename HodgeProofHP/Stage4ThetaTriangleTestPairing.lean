import HodgeProofHP.Stage4ThetaTriangleTestVector

/-!
The test-vector pairing is four times the kernel integral on the square.
Cauchy-Schwarz bounds this pairing by the norm of the operator action.
-/

noncomputable section

namespace HodgeProofHP

open MeasureTheory

def hpThetaTriangleKernelSquareIntegral : ℂ :=
  ∫ x in hpThetaTriangleTestInterval,
    ∫ y in hpThetaTriangleTestInterval,
      hpThetaHankelKernel x y ∂hpThetaHankelMeasure
        ∂hpThetaHankelMeasure

theorem hpThetaTriangleTestVector_inner_eq_square_integral :
    inner ℂ hpThetaTriangleTestVector
      (hpThetaHankelOperator hpThetaTriangleTestVector) =
        (4 : ℂ) * hpThetaTriangleKernelSquareIntegral := by
  classical
  rw [MeasureTheory.L2.inner_def]
  calc
    (∫ x, inner ℂ (hpThetaTriangleTestVector x)
        (hpThetaHankelOperator hpThetaTriangleTestVector x)
          ∂hpThetaHankelMeasure) =
        ∫ x, hpThetaTriangleTestInterval.indicator
          (fun x => (4 : ℂ) *
            ∫ y in hpThetaTriangleTestInterval,
              hpThetaHankelKernel x y ∂hpThetaHankelMeasure) x
                ∂hpThetaHankelMeasure := by
      apply integral_congr_ae
      filter_upwards
        [hpThetaTriangleTestVector_coeFn_ae,
         hpThetaTriangleTestVector_operator_coeFn_ae]
        with x hf ha
      rw [hf, ha]
      by_cases hx : x ∈ hpThetaTriangleTestInterval
      · have hstar : (starRingEnd ℂ) (2 : ℂ) = 2 := by
          calc
            (starRingEnd ℂ) (2 : ℂ) =
                (starRingEnd ℂ) ((1 : ℂ) + 1) := by
              congr 1
              norm_num
            _ = (1 : ℂ) + 1 := by
              rw [map_add, map_one]
            _ = 2 := by norm_num
        simp [hpThetaTriangleTestFunction, hx, hstar] <;> ring
      · simp [hpThetaTriangleTestFunction, hx]
    _ = ∫ x in hpThetaTriangleTestInterval,
        (4 : ℂ) *
          ∫ y in hpThetaTriangleTestInterval,
            hpThetaHankelKernel x y ∂hpThetaHankelMeasure
              ∂hpThetaHankelMeasure := by
      rw [integral_indicator hpThetaTriangleTestInterval_measurable]
    _ = (4 : ℂ) * hpThetaTriangleKernelSquareIntegral := by
      rw [integral_const_mul]
      rfl

theorem hpThetaTriangleTestVector_inner_norm_le_action_norm :
    ‖inner ℂ hpThetaTriangleTestVector
      (hpThetaHankelOperator hpThetaTriangleTestVector)‖ ≤
        ‖hpThetaHankelOperator hpThetaTriangleTestVector‖ := by
  have h :
      ‖inner ℂ hpThetaTriangleTestVector
        (hpThetaHankelOperator hpThetaTriangleTestVector)‖ ≤
      ‖hpThetaTriangleTestVector‖ *
        ‖hpThetaHankelOperator hpThetaTriangleTestVector‖ :=
    norm_inner_le_norm hpThetaTriangleTestVector
      (hpThetaHankelOperator hpThetaTriangleTestVector)
  simpa only [hpThetaTriangleTestVector_norm, one_mul] using h

theorem hpThetaTriangleTestVector_inner_re_le_action_norm :
    (inner ℂ hpThetaTriangleTestVector
      (hpThetaHankelOperator hpThetaTriangleTestVector)).re ≤
        ‖hpThetaHankelOperator hpThetaTriangleTestVector‖ := by
  have h :
      (inner ℂ hpThetaTriangleTestVector
        (hpThetaHankelOperator hpThetaTriangleTestVector)).re ≤
      ‖hpThetaTriangleTestVector‖ *
        ‖hpThetaHankelOperator hpThetaTriangleTestVector‖ :=
    re_inner_le_norm (𝕜 := ℂ) hpThetaTriangleTestVector
      (hpThetaHankelOperator hpThetaTriangleTestVector)
  simpa only [hpThetaTriangleTestVector_norm, one_mul] using h

theorem hpThetaTriangleTestVector_action_norm_le_opNorm :
    ‖hpThetaHankelOperator hpThetaTriangleTestVector‖ ≤
      ‖hpThetaHankelOperator‖ := by
  have h := hpThetaHankelOperator.le_opNorm hpThetaTriangleTestVector
  simpa only [hpThetaTriangleTestVector_norm, mul_one] using h

theorem hpThetaTriangleKernelSquareIntegral_re_le_action_norm :
    ((4 : ℂ) * hpThetaTriangleKernelSquareIntegral).re ≤
      ‖hpThetaHankelOperator hpThetaTriangleTestVector‖ := by
  rw [← hpThetaTriangleTestVector_inner_eq_square_integral]
  exact hpThetaTriangleTestVector_inner_re_le_action_norm

#print axioms hpThetaTriangleTestVector_inner_eq_square_integral
#print axioms hpThetaTriangleTestVector_inner_norm_le_action_norm
#print axioms hpThetaTriangleTestVector_inner_re_le_action_norm
#print axioms hpThetaTriangleTestVector_action_norm_le_opNorm
#print axioms hpThetaTriangleKernelSquareIntegral_re_le_action_norm

end HodgeProofHP
