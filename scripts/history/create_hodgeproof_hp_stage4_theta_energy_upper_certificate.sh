#!/usr/bin/env bash
set -euo pipefail

target="HodgeProofHP/Stage4ThetaEnergyUpperCertificate.lean"
if [ -f "$target" ]; then
  cp -p "$target" "$target.before_update_$(date +%Y%m%d_%H%M%S)"
fi

cat > "$target" <<'LEAN'
import HodgeProofHP.Stage4ThetaEnergyFiniteIntegralUpper
import HodgeProofHP.Stage4ThetaEnergyTailPointwise
import HodgeProofHP.Stage4ThetaFirstTraceMoments
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
A numerical upper certificate for the full theta Hankel energy.
The finite interval certificate and an integrable exponential tail
are combined without assuming any numerical energy bound.
-/

noncomputable section

open MeasureTheory

namespace HodgeProofHP

def hpThetaEnergyTailEnvelope (u : ℝ) : ℝ :=
  (1 / 1000000 : ℝ) * Real.exp (-(u - 1))

theorem hpThetaEnergyTailEnvelope_eq (u : ℝ) :
    hpThetaEnergyTailEnvelope u =
      ((1 / 1000000 : ℝ) * Real.exp 1) * Real.exp (-u) := by
  unfold hpThetaEnergyTailEnvelope
  rw [show -(u - 1) = 1 + (-u) by ring, Real.exp_add]
  ring

theorem hpThetaEnergyTailEnvelope_integrableOn :
    IntegrableOn hpThetaEnergyTailEnvelope (Set.Ioi 1) volume := by
  have h := (integrableOn_exp_neg_Ioi (1 : ℝ)).const_mul
    ((1 / 1000000 : ℝ) * Real.exp 1)
  have heq :
      hpThetaEnergyTailEnvelope =
        fun u : ℝ =>
          ((1 / 1000000 : ℝ) * Real.exp 1) * Real.exp (-u) := by
    funext u
    exact hpThetaEnergyTailEnvelope_eq u
  rw [heq]
  exact h

theorem hpThetaEnergyTailEnvelope_integral :
    (∫ u in Set.Ioi (1 : ℝ), hpThetaEnergyTailEnvelope u) =
      (1 / 1000000 : ℝ) := by
  have heq :
      hpThetaEnergyTailEnvelope =
        fun u : ℝ =>
          ((1 / 1000000 : ℝ) * Real.exp 1) * Real.exp (-u) := by
    funext u
    exact hpThetaEnergyTailEnvelope_eq u
  rw [heq, integral_const_mul, integral_exp_neg_Ioi]
  have hid : Real.exp 1 * Real.exp (-1) = 1 := by
    rw [← Real.exp_add]
    norm_num
  calc
    ((1 / 1000000 : ℝ) * Real.exp 1) * Real.exp (-1) =
        (1 / 1000000 : ℝ) * (Real.exp 1 * Real.exp (-1)) := by ring
    _ = (1 / 1000000 : ℝ) := by rw [hid, mul_one]

theorem hpThetaEnergyTail_integrand_le_envelope
    (u : ℝ) (hu : 1 ≤ u) :
    hpThetaEnergyUpperIntegrand u ≤ hpThetaEnergyTailEnvelope u := by
  have huexp : u ≤ Real.exp (u - 1) := by
    have h := Real.add_one_le_exp (u - 1)
    linarith
  have hweighted :
      u * Real.exp (-2 * (u - 1)) ≤ Real.exp (-(u - 1)) := by
    calc
      u * Real.exp (-2 * (u - 1)) ≤
          Real.exp (u - 1) * Real.exp (-2 * (u - 1)) :=
        mul_le_mul_of_nonneg_right huexp
          (le_of_lt (Real.exp_pos _))
      _ = Real.exp (-(u - 1)) := by
        rw [← Real.exp_add]
        congr 1
        ring
  have h := mul_le_mul_of_nonneg_left hweighted
    (by norm_num : (0 : ℝ) ≤ 1 / 1000000)
  calc
    hpThetaEnergyUpperIntegrand u ≤
        (1 / 1000000 : ℝ) * u * Real.exp (-2 * (u - 1)) :=
      hpThetaEnergyTail_integrand_upper u hu
    _ ≤ hpThetaEnergyTailEnvelope u := by
      unfold hpThetaEnergyTailEnvelope
      simpa only [mul_assoc] using h

theorem hpThetaEnergyUpperIntegrand_integrableOn_positive :
    IntegrableOn hpThetaEnergyUpperIntegrand (Set.Ioi 0) volume := by
  have heq :
      hpThetaEnergyUpperIntegrand =
        (fun u : ℝ =>
          u * hpRiemannThetaDifferentialKernel u ^ 2) := by
    funext u
    rfl
  rw [heq]
  exact hpRiemannThetaDifferentialKernel_hankel_weight_integrableOn


theorem hpThetaEnergyUpperIntegrand_integrableOn_tail :
    IntegrableOn hpThetaEnergyUpperIntegrand (Set.Ioi 1) volume := by
  apply hpThetaEnergyUpperIntegrand_integrableOn_positive.mono_set
  intro u hu
  exact lt_trans (by norm_num : (0 : ℝ) < 1) hu

theorem hpThetaEnergyTail_integral_le_one_millionth :
    (∫ u in Set.Ioi (1 : ℝ), hpThetaEnergyUpperIntegrand u) ≤
      (1 / 1000000 : ℝ) := by
  have h :=
    integral_mono_ae
      hpThetaEnergyUpperIntegrand_integrableOn_tail
      hpThetaEnergyTailEnvelope_integrableOn
      (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
        exact hpThetaEnergyTail_integrand_le_envelope u (le_of_lt hu))
  rw [hpThetaEnergyTailEnvelope_integral] at h
  exact h

theorem hpThetaFirstTraceEnergy_le_upper_certificate :
    hpThetaFirstTraceEnergy ≤
      (1080380018191215381377 / 12800000000000000000000 : ℝ) +
        (1 / 1000000 : ℝ) := by
  have hsplit := intervalIntegral.integral_interval_add_Ioi
    (a := (0 : ℝ)) (b := (1 : ℝ))
    hpThetaEnergyUpperIntegrand_integrableOn_positive
    hpThetaEnergyUpperIntegrand_integrableOn_tail
  calc
    hpThetaFirstTraceEnergy =
        (∫ u in (0 : ℝ)..1, hpThetaEnergyUpperIntegrand u) +
          (∫ u in Set.Ioi (1 : ℝ), hpThetaEnergyUpperIntegrand u) := by
      unfold hpThetaFirstTraceEnergy
      simpa only [hpThetaEnergyUpperIntegrand] using hsplit.symm
    _ ≤
        (1080380018191215381377 / 12800000000000000000000 : ℝ) +
          (1 / 1000000 : ℝ) :=
      add_le_add
        hpThetaEnergyUpper_integral_zero_one_le_certificate
        hpThetaEnergyTail_integral_le_one_millionth

theorem hpThetaFirstTraceEnergy_lt_seventeen_twoHundredths :
    hpThetaFirstTraceEnergy < (17 / 200 : ℝ) := by
  exact lt_of_le_of_lt
    hpThetaFirstTraceEnergy_le_upper_certificate (by norm_num)

#print axioms hpThetaEnergyTail_integral_le_one_millionth
#print axioms hpThetaFirstTraceEnergy_le_upper_certificate
#print axioms hpThetaFirstTraceEnergy_lt_seventeen_twoHundredths

end HodgeProofHP
LEAN

mkdir -p stage4_fourth_certificate_build_logs
log="stage4_fourth_certificate_build_logs/energy_upper_certificate.log"

if lake build HodgeProofHP.Stage4ThetaEnergyUpperCertificate >"$log" 2>&1; then
  tail -n 40 "$log"
  printf '%s\n' 'PASS: Stage4ThetaEnergyUpperCertificate'
else
  tail -n 100 "$log"
  printf 'STOP: energy upper certificate failed; log: %s\n' "$log"
  exit 1
fi
