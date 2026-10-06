import HodgeProofHP.Stage4ThetaTraceRemainingBound
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
Finite-interval integration by parts for the second moment
of the theta differential kernel.
-/

namespace HodgeProofHP

open MeasureTheory

theorem hpThetaSecondMoment_boundary_primitive_hasDerivAt (u : ℝ) :
    HasDerivAt
      (fun x : ℝ =>
        x ^ 2 * deriv hpRiemannThetaLogProfile x -
          2 * x * hpRiemannThetaLogProfile x)
      (u ^ 2 * deriv (deriv hpRiemannThetaLogProfile) u -
        2 * hpRiemannThetaLogProfile u) u := by
  have hB :
      HasDerivAt hpRiemannThetaLogProfile
        (deriv hpRiemannThetaLogProfile u) u :=
    (hpRiemannThetaLogProfile_differentiable u).hasDerivAt
  have hB' :
      HasDerivAt (deriv hpRiemannThetaLogProfile)
        (deriv (deriv hpRiemannThetaLogProfile) u) u :=
    (hpRiemannThetaLogProfile_deriv_differentiable u).hasDerivAt
  have hleft := ((hasDerivAt_id u).pow 2).mul hB'
  have hright :=
    ((hasDerivAt_const u (2 : ℝ)).mul (hasDerivAt_id u)).mul hB
  convert hleft.sub hright using 1
  · funext x
    simp only [Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, id_eq] <;> ring
  · simp only [Pi.mul_apply, Pi.pow_apply, id_eq, Nat.cast_ofNat] <;>
      norm_num <;> ring

theorem hpRiemannThetaLogProfile_secondDeriv_finite_secondMoment_ibp
    (R : ℝ) :
    (∫ u in (0 : ℝ)..R,
      u ^ 2 * deriv (deriv hpRiemannThetaLogProfile) u) =
      R ^ 2 * deriv hpRiemannThetaLogProfile R -
        2 * R * hpRiemannThetaLogProfile R +
        2 * (∫ u in (0 : ℝ)..R,
          hpRiemannThetaLogProfile u) := by
  have hleft :
      IntervalIntegrable
        (fun u : ℝ =>
          u ^ 2 * deriv (deriv hpRiemannThetaLogProfile) u)
        volume 0 R :=
    ((continuous_id.pow 2).mul
      hpRiemannThetaLogProfile_secondDeriv_continuous).intervalIntegrable 0 R
  have hright :
      IntervalIntegrable
        (fun u : ℝ => 2 * hpRiemannThetaLogProfile u)
        volume 0 R :=
    (continuous_const.mul
      hpRiemannThetaLogProfile_continuous).intervalIntegrable 0 R
  have h :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (a := (0 : ℝ)) (b := R)
      (fun u hu => hpThetaSecondMoment_boundary_primitive_hasDerivAt u)
      (hleft.sub hright)
  rw [intervalIntegral.integral_sub hleft hright,
    intervalIntegral.integral_const_mul] at h
  simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    zero_mul, mul_zero, sub_zero] at h
  linarith

theorem hpRiemannThetaDifferentialKernel_finite_secondMoment_ibp
    (R : ℝ) :
    (∫ u in (0 : ℝ)..R,
      u ^ 2 * hpRiemannThetaDifferentialKernel u) =
      R ^ 2 * deriv hpRiemannThetaLogProfile R -
        2 * R * hpRiemannThetaLogProfile R +
        2 * (∫ u in (0 : ℝ)..R,
          hpRiemannThetaLogProfile u) -
        (1 / 4 : ℝ) * (∫ u in (0 : ℝ)..R,
          u ^ 2 * hpRiemannThetaLogProfile u) := by
  have hleft :
      IntervalIntegrable
        (fun u : ℝ =>
          u ^ 2 * deriv (deriv hpRiemannThetaLogProfile) u)
        volume 0 R :=
    ((continuous_id.pow 2).mul
      hpRiemannThetaLogProfile_secondDeriv_continuous).intervalIntegrable 0 R
  have hweighted :
      IntervalIntegrable
        (fun u : ℝ => u ^ 2 * hpRiemannThetaLogProfile u)
        volume 0 R :=
    ((continuous_id.pow 2).mul
      hpRiemannThetaLogProfile_continuous).intervalIntegrable 0 R
  have hright :
      IntervalIntegrable
        (fun u : ℝ =>
          (1 / 4 : ℝ) * (u ^ 2 * hpRiemannThetaLogProfile u))
        volume 0 R :=
    (continuous_const.mul
      ((continuous_id.pow 2).mul
        hpRiemannThetaLogProfile_continuous)).intervalIntegrable 0 R
  have hfun :
      (fun u : ℝ =>
        u ^ 2 * hpRiemannThetaDifferentialKernel u) =
      (fun u : ℝ =>
        u ^ 2 * deriv (deriv hpRiemannThetaLogProfile) u -
          (1 / 4 : ℝ) * (u ^ 2 * hpRiemannThetaLogProfile u)) := by
    funext u
    unfold hpRiemannThetaDifferentialKernel
    ring
  rw [hfun, intervalIntegral.integral_sub hleft hright,
    intervalIntegral.integral_const_mul,
    hpRiemannThetaLogProfile_secondDeriv_finite_secondMoment_ibp]

#print axioms hpThetaSecondMoment_boundary_primitive_hasDerivAt
#print axioms hpRiemannThetaLogProfile_secondDeriv_finite_secondMoment_ibp
#print axioms hpRiemannThetaDifferentialKernel_finite_secondMoment_ibp

end HodgeProofHP
