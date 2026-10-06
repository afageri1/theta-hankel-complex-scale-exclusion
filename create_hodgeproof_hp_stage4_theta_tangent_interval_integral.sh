#!/usr/bin/env bash
set -euo pipefail

lake build HodgeProofHP.Stage4ThetaProfileGeometricUpperBound

target="HodgeProofHP/Stage4ThetaTangentIntervalIntegral.lean"

if [ -f "$target" ]; then
  cp -p "$target" "$target.before_update_$(date +%Y%m%d_%H%M%S)"
fi

cat > "$target" <<'LEAN'
import HodgeProofHP.Stage4ThetaProfileGeometricUpperBound
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
Exact finite-interval integrals of Gaussian tangent envelopes,
with upper bounds for the theta logarithmic profile.
-/

namespace HodgeProofHP

open MeasureTheory

theorem hpThetaTangent_exponential_intervalIntegral
    (C k l p q : ℝ) (hk : k ≠ 0) :
    (∫ u in p..q, C * Real.exp (-k * (u - l))) =
      C / k *
        (Real.exp (-k * (p - l)) -
          Real.exp (-k * (q - l))) := by
  have hderiv :
      ∀ u : ℝ,
        HasDerivAt
          (fun x : ℝ => -(C / k) * Real.exp (-k * (x - l)))
          (C * Real.exp (-k * (u - l))) u := by
    intro u
    have harg :
        HasDerivAt (fun x : ℝ => -k * (x - l)) (-k) u := by
      simpa only [id_eq, mul_one] using
        ((hasDerivAt_id u).sub_const l).const_mul (-k)
    convert harg.exp.const_mul (-(C / k)) using 1 <;>
      field_simp [hk] <;> ring
  have hcont :
      Continuous (fun u : ℝ => C * Real.exp (-k * (u - l))) := by
    fun_prop
  calc
    (∫ u in p..q, C * Real.exp (-k * (u - l))) =
        -(C / k) * Real.exp (-k * (q - l)) -
          (-(C / k) * Real.exp (-k * (p - l))) :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun u _ => hderiv u)
        (hcont.intervalIntegrable p q)
    _ = C / k *
        (Real.exp (-k * (p - l)) -
          Real.exp (-k * (q - l))) := by
      ring

theorem hpThetaGaussianTangentEnvelope_continuous
    (a l : ℝ) :
    Continuous (hpThetaGaussianTangentEnvelope a l) := by
  unfold hpThetaGaussianTangentEnvelope
  fun_prop

theorem hpThetaGaussianTangentEnvelope_intervalIntegral
    (a l p q : ℝ)
    (hk : 2 * a * Real.exp (2 * l) - 1 / 2 ≠ 0) :
    (∫ u in p..q, hpThetaGaussianTangentEnvelope a l u) =
      (2 * Real.exp (l / 2 - a * Real.exp (2 * l))) /
        (2 * a * Real.exp (2 * l) - 1 / 2) *
        (Real.exp
            (-(2 * a * Real.exp (2 * l) - 1 / 2) * (p - l)) -
          Real.exp
            (-(2 * a * Real.exp (2 * l) - 1 / 2) * (q - l))) := by
  unfold hpThetaGaussianTangentEnvelope
  exact hpThetaTangent_exponential_intervalIntegral
    (2 * Real.exp (l / 2 - a * Real.exp (2 * l)))
    (2 * a * Real.exp (2 * l) - 1 / 2)
    l p q hk

theorem hpThetaProfile_intervalIntegral_le_tangent
    (l p q : ℝ) (hp : 0 ≤ p) (hpq : p ≤ q) :
    (∫ u in p..q, hpRiemannThetaLogProfile u) ≤
      ∫ u in p..q,
        hpThetaGaussianTangentEnvelope Real.pi l u /
          (1 - Real.exp (-Real.pi)) := by
  have hcont :
      Continuous
        (fun u : ℝ =>
          hpThetaGaussianTangentEnvelope Real.pi l u /
            (1 - Real.exp (-Real.pi))) :=
    (hpThetaGaussianTangentEnvelope_continuous Real.pi l).div_const _
  apply intervalIntegral.integral_mono_on hpq
    (hpRiemannThetaLogProfile_continuous.intervalIntegrable p q)
    (hcont.intervalIntegrable p q)
  intro u hu
  exact hpRiemannThetaLogProfile_le_geometric_tangent_upper
    l u (le_trans hp hu.1)

#print axioms hpThetaTangent_exponential_intervalIntegral
#print axioms hpThetaGaussianTangentEnvelope_intervalIntegral
#print axioms hpThetaProfile_intervalIntegral_le_tangent

end HodgeProofHP
LEAN

lake env lean "$target"
lake build HodgeProofHP.Stage4ThetaTangentIntervalIntegral

printf '%s\n' 'PASS: Stage4ThetaTangentIntervalIntegral'
