#!/usr/bin/env bash
set -euo pipefail

if [[ ! -f lakefile.lean && ! -f lakefile.toml ]]; then
  echo "STOP: run from ~/hodgeproof-hp"
  exit 1
fi

lake build HodgeProofHP.Stage4ThetaHankelSelfAdjoint

target="HodgeProofHP/Stage4ThetaFirstTraceMoments.lean"

if [[ -f "$target" ]]; then
  backup="${target}.before_create_$(date +%Y%m%d_%H%M%S)_$$"
  cp "$target" "$backup"
  echo "BACKUP: $backup"
fi

cat > "$target" <<'LEAN'
import HodgeProofHP.Stage4ThetaHankelSelfAdjoint

/-!
Moment quantities for the first-trace comparison.

The zeroth-moment identity follows from the established cosine
representation. Numerical separation bounds remain explicit
hypotheses; no external computation is imported as a proof.
-/

noncomputable section

namespace HodgeProofHP

open MeasureTheory

/-- Zeroth moment of the differential theta kernel. -/
def hpThetaPhiMomentZero : ℝ :=
  ∫ u in Set.Ioi 0, hpRiemannThetaDifferentialKernel u

/-- Second moment of the differential theta kernel. -/
def hpThetaPhiMomentTwo : ℝ :=
  ∫ u in Set.Ioi 0,
    u ^ 2 * hpRiemannThetaDifferentialKernel u

/-- Weighted square integral used in the first-trace test. -/
def hpThetaFirstTraceEnergy : ℝ :=
  ∫ u in Set.Ioi 0,
    u * hpRiemannThetaDifferentialKernel u ^ 2

/-- Moment ratio to be related to the second derivative of Xi. -/
def hpThetaXiMomentRatio : ℝ :=
  hpThetaPhiMomentTwo / (2 * hpThetaPhiMomentZero)

theorem hpThetaPhiMomentZero_cast_eq_xi_zero :
    (hpThetaPhiMomentZero : ℂ) =
      hpRiemannXiCritical 0 := by
  have h :=
    hpRiemannXiCritical_eq_differentialKernel_cosine_integral
      (0 : ℂ)
  simp only [zero_mul, Complex.cos_zero, mul_one] at h
  have hcast :
      (∫ u in Set.Ioi 0,
        (hpRiemannThetaDifferentialKernel u : ℂ)) =
          (hpThetaPhiMomentZero : ℂ) := by
    exact integral_complex_ofReal
      (f := hpRiemannThetaDifferentialKernel)
      (μ := volume.restrict (Set.Ioi 0))
  exact hcast.symm.trans h.symm

theorem hpThetaPhiMomentZero_eq_xi_zero_re :
    hpThetaPhiMomentZero =
      (hpRiemannXiCritical 0).re := by
  have h := congrArg Complex.re
    hpThetaPhiMomentZero_cast_eq_xi_zero
  simpa using h

/--
A separation criterion. Its moment and energy bounds are
hypotheses, not consequences of the external interval script.
-/
theorem hpThetaFirstTraceEnergy_ne_ratio_of_bounds
    (hzero : 0 < hpThetaPhiMomentZero)
    (htwo :
      hpThetaPhiMomentTwo <
        (3 / 50 : ℝ) * hpThetaPhiMomentZero)
    (henergy : (7 / 100 : ℝ) < hpThetaFirstTraceEnergy) :
    hpThetaFirstTraceEnergy ≠ hpThetaXiMomentRatio := by
  have hden : 0 < 2 * hpThetaPhiMomentZero := by
    positivity
  have hratio : hpThetaXiMomentRatio < (3 / 100 : ℝ) := by
    unfold hpThetaXiMomentRatio
    apply (div_lt_iff₀ hden).2
    nlinarith [htwo]
  intro heq
  rw [heq] at henergy
  linarith

#print axioms hpThetaPhiMomentZero_cast_eq_xi_zero
#print axioms hpThetaPhiMomentZero_eq_xi_zero_re
#print axioms hpThetaFirstTraceEnergy_ne_ratio_of_bounds

end HodgeProofHP
LEAN

lake env lean "$target"
lake build HodgeProofHP.Stage4ThetaFirstTraceMoments

echo "PASS: Stage4ThetaFirstTraceMoments"
