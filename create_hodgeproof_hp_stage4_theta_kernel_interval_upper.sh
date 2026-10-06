#!/usr/bin/env bash
set -euo pipefail

target="HodgeProofHP/Stage4ThetaKernelIntervalUpper.lean"
if [ -f "$target" ]; then
  cp -p "$target" "$target.before_update_$(date +%Y%m%d_%H%M%S)"
fi

cat > "$target" <<'LEAN'
import HodgeProofHP.Stage4ThetaKernelFirstTermUpper

/-!
Interval upper certificates for the theta differential kernel.
The exponential inputs can be certified using rational Taylor bounds.
-/

noncomputable section

namespace HodgeProofHP

/-- Repeated powering turns a small-argument lower bound into
an upper bound for a negative exponential. -/
theorem hpThetaKernelUpper_exp_neg_of_lower_power
    (t v W : ℝ)
    (hv : 0 < v)
    (hlower : v ≤ Real.exp (t / 32))
    (hcert : 1 ≤ W * v ^ 32) :
    Real.exp (-t) ≤ W := by
  have hvpow : 0 < v ^ 32 := pow_pos hv _
  have hW : 0 ≤ W := by
    by_contra h
    have hneg : W * v ^ 32 < 0 :=
      mul_neg_of_neg_of_pos (lt_of_not_ge h) hvpow
    linarith
  have hpow :
      v ^ 32 ≤ (Real.exp (t / 32)) ^ 32 :=
    pow_le_pow_left₀ (le_of_lt hv) hlower 32
  have hexp :
      (Real.exp (t / 32)) ^ 32 = Real.exp t := by
    rw [hpThetaKernelUpper_exp_pow]
    congr 1
    norm_num
  rw [hexp] at hpow
  have hproduct := mul_le_mul_of_nonneg_left hpow hW
  have hid : Real.exp (-t) * Real.exp t = 1 := by
    rw [← Real.exp_add]
    simp
  have hepos := Real.exp_pos t
  nlinarith

/-- Upper bound on one interval, preserving the negative linear term
in the Gaussian kernel coefficient. -/
theorem hpThetaKernel_interval_upper_of_exp_bounds
    (l r L U W u : ℝ)
    (hl : 0 ≤ l)
    (hlu : l ≤ u)
    (hur : u ≤ r)
    (hL : 0 ≤ L)
    (hU : 0 ≤ U)
    (hW : 0 ≤ W)
    (hleft : L ≤ Real.exp (2 * l))
    (hright : Real.exp (2 * r) ≤ U)
    (hexp : Real.exp (r / 2 - (157 / 50 : ℝ) * L) ≤ W) :
    hpRiemannThetaDifferentialKernel u ≤
      (12183 / 12151 : ℝ) *
        (4 * (63 / 20 : ℝ) ^ 2 * U ^ 2 -
          6 * (157 / 50 : ℝ) * L) * (2 * W) := by
  have hu : 0 ≤ u := le_trans hl hlu
  have hpiLower : (157 / 50 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d2
    linarith
  have hpiUpper : Real.pi ≤ (63 / 20 : ℝ) := by
    have h := Real.pi_lt_d2
    linarith
  have hleftu : L ≤ Real.exp (2 * u) :=
    le_trans hleft
      (Real.exp_le_exp.mpr (by linarith))
  have hrightu : Real.exp (2 * u) ≤ U :=
    le_trans (Real.exp_le_exp.mpr (by linarith)) hright
  let b : ℝ := Real.pi * Real.exp (2 * u)
  let a : ℝ :=
    4 * (63 / 20 : ℝ) ^ 2 * U ^ 2 -
      6 * (157 / 50 : ℝ) * L
  have hb0 : 0 ≤ b := by
    dsimp [b]
    positivity
  have hbLower : (157 / 50 : ℝ) * L ≤ b := by
    dsimp [b]
    exact mul_le_mul hpiLower hleftu hL
      (le_of_lt Real.pi_pos)
  have hbUpper : b ≤ (63 / 20 : ℝ) * U := by
    dsimp [b]
    exact mul_le_mul hpiUpper hrightu
      (le_of_lt (Real.exp_pos _)) (by norm_num)
  have hbSq :
      b ^ 2 ≤ ((63 / 20 : ℝ) * U) ^ 2 :=
    pow_le_pow_left₀ hb0 hbUpper 2
  have hcoefficient : 4 * b ^ 2 - 6 * b ≤ a := by
    dsimp [a]
    nlinarith [hbSq, hbLower]
  have ht : 1 ≤ Real.exp (2 * u) := by
    simpa using
      Real.exp_le_exp.mpr (show 0 ≤ 2 * u by linarith)
  have hpi3 : 3 ≤ Real.pi := by
    have h := Real.pi_gt_d2
    linarith
  have hb3 : 3 ≤ b := by
    have h := mul_le_mul_of_nonneg_left ht
      (le_of_lt Real.pi_pos)
    dsimp [b]
    nlinarith
  have hcoefficient0 : 0 ≤ 4 * b ^ 2 - 6 * b := by
    nlinarith
  have ha : 0 ≤ a := le_trans hcoefficient0 hcoefficient
  have hprofile :
      hpThetaGaussianProfile Real.pi u ≤ 2 * W := by
    unfold hpThetaGaussianProfile
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply le_trans _ hexp
    apply Real.exp_le_exp.mpr
    dsimp [b] at hbLower
    linarith
  have hprofile0 : 0 ≤ hpThetaGaussianProfile Real.pi u := by
    unfold hpThetaGaussianProfile
    positivity
  have hterm :
      hpThetaGaussianKernelTerm Real.pi u ≤ a * (2 * W) := by
    have h :=
      mul_le_mul hcoefficient hprofile hprofile0 ha
    simpa only [hpThetaGaussianKernelTerm, b, pow_two,
      mul_assoc, mul_left_comm, mul_comm] using h
  calc
    hpRiemannThetaDifferentialKernel u ≤
        (12183 / 12151 : ℝ) *
          hpThetaGaussianKernelTerm Real.pi u :=
      hpThetaPhi_le_firstTerm_upper u hu
    _ ≤ (12183 / 12151 : ℝ) * (a * (2 * W)) :=
      mul_le_mul_of_nonneg_left hterm (by norm_num)
    _ = _ := by
      dsimp [a]
      ring

/-- A rationally checkable certificate for an interval upper bound. -/
theorem hpThetaKernel_rational_interval_upper_certificate
    (l r L U v W H : ℝ)
    (hl : 0 ≤ l)
    (hL : 0 ≤ L)
    (hU : 0 ≤ U)
    (hv : 0 < v)
    (hW : 0 ≤ W)
    (hleft : L ≤ Real.exp (2 * l))
    (hright : Real.exp (2 * r) ≤ U)
    (hvexp :
      v ≤ Real.exp (((157 / 50 : ℝ) * L - r / 2) / 32))
    (hpower : 1 ≤ W * v ^ 32)
    (hfinal :
      (12183 / 12151 : ℝ) *
        (4 * (63 / 20 : ℝ) ^ 2 * U ^ 2 -
          6 * (157 / 50 : ℝ) * L) * (2 * W) ≤ H) :
    ∀ u : ℝ, l ≤ u → u ≤ r →
      hpRiemannThetaDifferentialKernel u ≤ H := by
  have hexp :
      Real.exp (r / 2 - (157 / 50 : ℝ) * L) ≤ W := by
    have h := hpThetaKernelUpper_exp_neg_of_lower_power
      ((157 / 50 : ℝ) * L - r / 2) v W hv hvexp hpower
    convert h using 1 <;> congr 1 <;> ring
  intro u hlu hur
  exact le_trans
    (hpThetaKernel_interval_upper_of_exp_bounds
      l r L U W u hl hlu hur hL hU hW hleft hright hexp)
    hfinal

#print axioms hpThetaKernelUpper_exp_neg_of_lower_power
#print axioms hpThetaKernel_interval_upper_of_exp_bounds
#print axioms hpThetaKernel_rational_interval_upper_certificate

end HodgeProofHP
LEAN

mkdir -p stage4_fourth_certificate_build_logs
log="stage4_fourth_certificate_build_logs/kernel_interval_upper.log"

if lake build HodgeProofHP.Stage4ThetaKernelIntervalUpper >"$log" 2>&1; then
  tail -n 40 "$log"
  printf '%s\n' 'PASS: Stage4ThetaKernelIntervalUpper'
else
  tail -n 100 "$log"
  printf 'STOP: build failed; log: %s\n' "$log"
  exit 1
fi
