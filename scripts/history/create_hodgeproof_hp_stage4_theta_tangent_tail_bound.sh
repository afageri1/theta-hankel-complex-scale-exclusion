#!/usr/bin/env bash
set -euo pipefail

lake build HodgeProofHP.Stage4ThetaTangentIntervalIntegral

target="HodgeProofHP/Stage4ThetaTangentTailBound.lean"

if [ -f "$target" ]; then
  cp -p "$target" "$target.before_update_$(date +%Y%m%d_%H%M%S)"
fi

cat > "$target" <<'LEAN'
import HodgeProofHP.Stage4ThetaTangentIntervalIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
Explicit upper bounds for tails of the theta logarithmic profile.
-/

namespace HodgeProofHP

open MeasureTheory Filter
open scoped Topology

theorem hpThetaTangent_exponential_intervalIntegral_le
    (C k l p q : ℝ) (hC : 0 ≤ C) (hk : 0 < k) :
    (∫ u in p..q, C * Real.exp (-k * (u - l))) ≤
      C / k * Real.exp (-k * (p - l)) := by
  rw [hpThetaTangent_exponential_intervalIntegral
    C k l p q (ne_of_gt hk)]
  have hfactor : 0 ≤ C / k :=
    div_nonneg hC (le_of_lt hk)
  apply mul_le_mul_of_nonneg_left _ hfactor
  linarith [Real.exp_pos (-k * (q - l))]

theorem hpThetaProfileTangent_rate_pos
    (l : ℝ) (hl : 0 ≤ l) :
    0 < 2 * Real.pi * Real.exp (2 * l) - 1 / 2 := by
  have ht : 1 ≤ Real.exp (2 * l) := by
    calc
      1 = Real.exp 0 := Real.exp_zero.symm
      _ ≤ Real.exp (2 * l) :=
        Real.exp_le_exp.mpr (by linarith)
  have hscaled :=
    mul_le_mul_of_nonneg_left ht
      (le_of_lt Real.pi_pos)
  have hpi := Real.pi_gt_three
  nlinarith [hscaled]

noncomputable def hpThetaProfileTangentTailBound
    (l p : ℝ) : ℝ :=
  ((2 * Real.exp (l / 2 - Real.pi * Real.exp (2 * l))) /
    (2 * Real.pi * Real.exp (2 * l) - 1 / 2) *
    Real.exp
      (-(2 * Real.pi * Real.exp (2 * l) - 1 / 2) * (p - l))) /
    (1 - Real.exp (-Real.pi))

theorem hpThetaProfile_intervalIntegral_le_tangent_tail
    (l p q : ℝ) (hl : 0 ≤ l)
    (hp : 0 ≤ p) (hpq : p ≤ q) :
    (∫ u in p..q, hpRiemannThetaLogProfile u) ≤
      hpThetaProfileTangentTailBound l p := by
  have henv :
      (∫ u in p..q, hpThetaGaussianTangentEnvelope Real.pi l u) ≤
        (2 * Real.exp (l / 2 - Real.pi * Real.exp (2 * l))) /
          (2 * Real.pi * Real.exp (2 * l) - 1 / 2) *
          Real.exp
            (-(2 * Real.pi * Real.exp (2 * l) - 1 / 2) *
              (p - l)) := by
    unfold hpThetaGaussianTangentEnvelope
    apply hpThetaTangent_exponential_intervalIntegral_le
    · positivity
    · exact hpThetaProfileTangent_rate_pos l hl
  have hinv :
      0 ≤ (1 - Real.exp (-Real.pi))⁻¹ :=
    inv_nonneg.mpr
      (le_of_lt hpThetaProfileGeometric_denominator_pos)
  calc
    (∫ u in p..q, hpRiemannThetaLogProfile u) ≤
        ∫ u in p..q,
          hpThetaGaussianTangentEnvelope Real.pi l u /
            (1 - Real.exp (-Real.pi)) :=
      hpThetaProfile_intervalIntegral_le_tangent l p q hp hpq
    _ = (∫ u in p..q,
          hpThetaGaussianTangentEnvelope Real.pi l u) /
            (1 - Real.exp (-Real.pi)) := by
      rw [intervalIntegral.integral_div]
    _ ≤ hpThetaProfileTangentTailBound l p := by
      unfold hpThetaProfileTangentTailBound
      simpa only [div_eq_mul_inv] using
        mul_le_mul_of_nonneg_right henv hinv

theorem hpThetaProfile_integrableOn_tail
    (p : ℝ) (hp : 0 ≤ p) :
    IntegrableOn hpRiemannThetaLogProfile (Set.Ioi p) volume := by
  have hzero :
      IntegrableOn hpRiemannThetaLogProfile (Set.Ioi 0) volume := by
    simpa only [zero_mul, Real.exp_zero, one_mul] using
      hpRiemannThetaLogProfile_exp_weighted_integrableOn 0
  apply hzero.mono_set
  intro u hu
  exact lt_of_le_of_lt hp hu

theorem hpThetaProfile_tail_integral_le_tangent
    (l p : ℝ) (hl : 0 ≤ l) (hp : 0 ≤ p) :
    (∫ u in Set.Ioi p, hpRiemannThetaLogProfile u) ≤
      hpThetaProfileTangentTailBound l p := by
  have hlim :
      Tendsto
        (fun R : ℝ => ∫ u in p..R, hpRiemannThetaLogProfile u)
        atTop
        (nhds (∫ u in Set.Ioi p, hpRiemannThetaLogProfile u)) :=
    intervalIntegral_tendsto_integral_Ioi p
      (hpThetaProfile_integrableOn_tail p hp)
      tendsto_id
  apply le_of_tendsto hlim
  filter_upwards [eventually_ge_atTop p] with R hR
  exact hpThetaProfile_intervalIntegral_le_tangent_tail
    l p R hl hp hR

theorem hpThetaProfile_tail_integral_le_tangent_at_endpoint
    (p : ℝ) (hp : 0 ≤ p) :
    (∫ u in Set.Ioi p, hpRiemannThetaLogProfile u) ≤
      (2 * Real.exp (p / 2 - Real.pi * Real.exp (2 * p))) /
        (2 * Real.pi * Real.exp (2 * p) - 1 / 2) /
        (1 - Real.exp (-Real.pi)) := by
  simpa only [hpThetaProfileTangentTailBound, sub_self,
    mul_zero, Real.exp_zero, mul_one] using
    hpThetaProfile_tail_integral_le_tangent p p hp hp

#print axioms hpThetaTangent_exponential_intervalIntegral_le
#print axioms hpThetaProfileTangent_rate_pos
#print axioms hpThetaProfile_intervalIntegral_le_tangent_tail
#print axioms hpThetaProfile_tail_integral_le_tangent
#print axioms hpThetaProfile_tail_integral_le_tangent_at_endpoint

end HodgeProofHP
LEAN

lake env lean "$target"
lake build HodgeProofHP.Stage4ThetaTangentTailBound

printf '%s\n' 'PASS: Stage4ThetaTangentTailBound'
