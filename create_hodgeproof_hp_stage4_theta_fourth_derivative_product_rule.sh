#!/usr/bin/env bash
set -euo pipefail

lake build HodgeProofHP.Stage4ThetaHankelSpectralProductHigherDerivativeLimits

target="HodgeProofHP/Stage4ThetaFourthDerivativeProductRule.lean"

if [ -f "$target" ]; then
  cp -p "$target" "$target.before_update_$(date +%Y%m%d_%H%M%S)"
fi

cat > "$target" <<'LEAN'
import HodgeProofHP.Stage4ThetaHankelSpectralProductHigherDerivativeLimits
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
Connect the project's iterated derivatives to mathlib and derive
the fourth-order product rule at zero when first derivatives vanish.
-/

namespace HodgeProofHP

theorem hpThetaIteratedComplexDeriv_eq_iteratedDeriv
    (n : ℕ) (f : ℂ → ℂ) :
    hpThetaIteratedComplexDeriv n f = iteratedDeriv n f := by
  induction n with
  | zero =>
      simp [hpThetaIteratedComplexDeriv]
  | succ n ih =>
      change deriv (hpThetaIteratedComplexDeriv n f) =
        iteratedDeriv (n + 1) f
      rw [ih, iteratedDeriv_succ]

theorem hpTheta_fourthDeriv_mul_zero
    (f g : ℂ → ℂ)
    (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g)
    (hdf0 : deriv f 0 = 0)
    (hdg0 : deriv g 0 = 0) :
    hpThetaIteratedComplexDeriv 4 (fun z => f z * g z) 0 =
      f 0 * hpThetaIteratedComplexDeriv 4 g 0 +
      6 * hpThetaIteratedComplexDeriv 2 f 0 *
        hpThetaIteratedComplexDeriv 2 g 0 +
      hpThetaIteratedComplexDeriv 4 f 0 * g 0 := by
  have hfc : ContDiffAt ℂ 4 f 0 :=
    (show ContDiff ℂ 4 f from hf.contDiff).contDiffAt
  have hgc : ContDiffAt ℂ 4 g 0 :=
    (show ContDiff ℂ 4 g from hg.contDiff).contDiffAt
  have h := iteratedDeriv_fun_mul (n := 4) (x := (0 : ℂ)) hfc hgc
  norm_num [Finset.sum_range_succ] at h
  have hchoose : Nat.choose 4 2 = 6 := by decide
  simp only [hchoose, Nat.cast_ofNat] at h
  simp only [hdf0, hdg0, mul_zero, zero_mul, add_zero, zero_add] at h
  simp only [hpThetaIteratedComplexDeriv_eq_iteratedDeriv]
  linear_combination h

theorem hpTheta_fourthDeriv_mul_normalized_zero
    (f g : ℂ → ℂ)
    (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g)
    (hf0 : f 0 = 1)
    (hg0 : g 0 = 1)
    (hdf0 : deriv f 0 = 0)
    (hdg0 : deriv g 0 = 0) :
    hpThetaIteratedComplexDeriv 4 (fun z => f z * g z) 0 =
      hpThetaIteratedComplexDeriv 4 g 0 +
      6 * hpThetaIteratedComplexDeriv 2 f 0 *
        hpThetaIteratedComplexDeriv 2 g 0 +
      hpThetaIteratedComplexDeriv 4 f 0 := by
  simpa only [hf0, hg0, one_mul, mul_one] using
    hpTheta_fourthDeriv_mul_zero f g hf hg hdf0 hdg0

#print axioms hpThetaIteratedComplexDeriv_eq_iteratedDeriv
#print axioms hpTheta_fourthDeriv_mul_zero
#print axioms hpTheta_fourthDeriv_mul_normalized_zero

end HodgeProofHP
LEAN

lake env lean "$target"
lake build HodgeProofHP.Stage4ThetaFourthDerivativeProductRule

printf '%s\n' 'PASS: Stage4ThetaFourthDerivativeProductRule'
