#!/usr/bin/env bash
set -euo pipefail

target="HodgeProofHP/Stage4ThetaEnergyTailPointwise.lean"
if [ -f "$target" ]; then
  cp -p "$target" "$target.before_update_$(date +%Y%m%d_%H%M%S)"
fi

cat > "$target" <<'LEAN'
import HodgeProofHP.Stage4ThetaKernelFirstTermUpper

/-!
Explicit exponential bounds for the theta kernel beyond one.
These bounds will control the remaining energy integral.
-/

noncomputable section

namespace HodgeProofHP

theorem hpThetaEnergyTail_exp_two_lower :
    (7 : ℝ) ≤ Real.exp 2 := by
  exact hpThetaTrace_exp_lower_of_taylor
    2 7 12 (by norm_num)
    (by norm_num [hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial])

theorem hpThetaEnergyTail_exp_seventeen_lower :
    (80000 : ℝ) ≤ Real.exp 17 := by
  exact hpThetaTrace_exp_lower_of_taylor
    17 80000 12 (by norm_num)
    (by norm_num [hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial])

theorem hpThetaEnergyTail_prefactor_bound :
    80 * Real.exp (-17) ≤ (1 / 1000 : ℝ) := by
  have h := mul_le_mul_of_nonneg_right
    hpThetaEnergyTail_exp_seventeen_lower
    (le_of_lt (Real.exp_pos (-17)))
  have hid : Real.exp 17 * Real.exp (-17) = 1 := by
    rw [← Real.exp_add]
    norm_num
  rw [hid] at h
  linarith

theorem hpThetaEnergyTail_kernel_rough_upper
    (u : ℝ) (hu : 0 ≤ u) :
    hpRiemannThetaDifferentialKernel u ≤
      80 * Real.exp ((9 / 2 : ℝ) * u -
        Real.pi * Real.exp (2 * u)) := by
  have hpiUpper : Real.pi ≤ (63 / 20 : ℝ) := by
    have h := Real.pi_lt_d2
    linarith
  have hpiSq : Real.pi ^ 2 ≤ (63 / 20 : ℝ) ^ 2 :=
    pow_le_pow_left₀ (le_of_lt Real.pi_pos) hpiUpper 2
  have hC :
      (12183 / 12151 : ℝ) * 8 * Real.pi ^ 2 ≤ 80 := by
    nlinarith [hpiSq]
  have hprofile0 : 0 ≤ hpThetaGaussianProfile Real.pi u := by
    unfold hpThetaGaussianProfile
    positivity
  have hterm :
      hpThetaGaussianKernelTerm Real.pi u ≤
        (4 * Real.pi ^ 2 * (Real.exp (2 * u)) ^ 2) *
          hpThetaGaussianProfile Real.pi u := by
    unfold hpThetaGaussianKernelTerm
    apply mul_le_mul_of_nonneg_right _ hprofile0
    have hnonneg : 0 ≤ 6 * Real.pi * Real.exp (2 * u) := by
      positivity
    linarith
  have he :
      (Real.exp (2 * u)) ^ 2 *
          Real.exp (u / 2 - Real.pi * Real.exp (2 * u)) =
        Real.exp ((9 / 2 : ℝ) * u -
          Real.pi * Real.exp (2 * u)) := by
    rw [hpThetaKernelUpper_exp_pow, ← Real.exp_add]
    congr 1
    ring
  calc
    hpRiemannThetaDifferentialKernel u ≤
        (12183 / 12151 : ℝ) *
          hpThetaGaussianKernelTerm Real.pi u :=
      hpThetaPhi_le_firstTerm_upper u hu
    _ ≤ (12183 / 12151 : ℝ) *
        ((4 * Real.pi ^ 2 * (Real.exp (2 * u)) ^ 2) *
          hpThetaGaussianProfile Real.pi u) :=
      mul_le_mul_of_nonneg_left hterm (by norm_num)
    _ = ((12183 / 12151 : ℝ) * 8 * Real.pi ^ 2) *
        ((Real.exp (2 * u)) ^ 2 *
          Real.exp (u / 2 - Real.pi * Real.exp (2 * u))) := by
      unfold hpThetaGaussianProfile
      ring
    _ = ((12183 / 12151 : ℝ) * 8 * Real.pi ^ 2) *
        Real.exp ((9 / 2 : ℝ) * u -
          Real.pi * Real.exp (2 * u)) := by rw [he]
    _ ≤ 80 * Real.exp ((9 / 2 : ℝ) * u -
        Real.pi * Real.exp (2 * u)) :=
      mul_le_mul_of_nonneg_right hC (le_of_lt (Real.exp_pos _))

theorem hpThetaEnergyTail_exp_tangent_lower
    (u : ℝ) (hu : 1 ≤ u) :
    7 * (1 + 2 * (u - 1)) ≤ Real.exp (2 * u) := by
  have ha : 0 ≤ 1 + 2 * (u - 1) := by linarith
  have ht : 1 + 2 * (u - 1) ≤ Real.exp (2 * (u - 1)) := by
    simpa only [add_comm] using Real.add_one_le_exp (2 * (u - 1))
  have he :
      Real.exp 2 * Real.exp (2 * (u - 1)) =
        Real.exp (2 * u) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    7 * (1 + 2 * (u - 1)) ≤
        Real.exp 2 * (1 + 2 * (u - 1)) :=
      mul_le_mul_of_nonneg_right hpThetaEnergyTail_exp_two_lower ha
    _ ≤ Real.exp 2 * Real.exp (2 * (u - 1)) :=
      mul_le_mul_of_nonneg_left ht (le_of_lt (Real.exp_pos _))
    _ = Real.exp (2 * u) := he

theorem hpThetaEnergyTail_kernel_upper
    (u : ℝ) (hu : 1 ≤ u) :
    hpRiemannThetaDifferentialKernel u ≤
      (1 / 1000 : ℝ) * Real.exp (-(u - 1)) := by
  have hu0 : 0 ≤ u := by linarith
  have hpiLower : (157 / 50 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d2
    linarith
  have ht := hpThetaEnergyTail_exp_tangent_lower u hu
  have hb := mul_le_mul_of_nonneg_left ht
    (by norm_num : (0 : ℝ) ≤ 157 / 50)
  have hp := mul_le_mul_of_nonneg_right hpiLower
    (le_of_lt (Real.exp_pos (2 * u)))
  have hexponent :
      (9 / 2 : ℝ) * u - Real.pi * Real.exp (2 * u) ≤
        -17 - (u - 1) := by
    nlinarith [hb, hp]
  calc
    hpRiemannThetaDifferentialKernel u ≤
        80 * Real.exp ((9 / 2 : ℝ) * u -
          Real.pi * Real.exp (2 * u)) :=
      hpThetaEnergyTail_kernel_rough_upper u hu0
    _ ≤ 80 * Real.exp (-17 - (u - 1)) :=
      mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr hexponent) (by norm_num)
    _ = (80 * Real.exp (-17)) * Real.exp (-(u - 1)) := by
      rw [sub_eq_add_neg, Real.exp_add]
      ring
    _ ≤ (1 / 1000 : ℝ) * Real.exp (-(u - 1)) :=
      mul_le_mul_of_nonneg_right hpThetaEnergyTail_prefactor_bound
        (le_of_lt (Real.exp_pos _))

theorem hpThetaEnergyTail_integrand_upper
    (u : ℝ) (hu : 1 ≤ u) :
    u * hpRiemannThetaDifferentialKernel u ^ 2 ≤
      (1 / 1000000 : ℝ) * u * Real.exp (-2 * (u - 1)) := by
  have hu0 : 0 ≤ u := by linarith
  have hphi0 : 0 ≤ hpRiemannThetaDifferentialKernel u :=
    le_of_lt (hpThetaPhi_pos_on_nonnegative u hu0)
  have hs := pow_le_pow_left₀ hphi0
    (hpThetaEnergyTail_kernel_upper u hu) 2
  have he :
      (Real.exp (-(u - 1))) ^ 2 =
        Real.exp (-2 * (u - 1)) := by
    rw [hpThetaKernelUpper_exp_pow]
    congr 1
    ring
  rw [mul_pow, he] at hs
  have h := mul_le_mul_of_nonneg_left hs hu0
  convert h using 1 <;> norm_num <;> ring

#print axioms hpThetaEnergyTail_kernel_upper
#print axioms hpThetaEnergyTail_integrand_upper

end HodgeProofHP
LEAN

mkdir -p stage4_fourth_certificate_build_logs
log="stage4_fourth_certificate_build_logs/energy_tail_pointwise.log"

if lake build HodgeProofHP.Stage4ThetaEnergyTailPointwise >"$log" 2>&1; then
  tail -n 35 "$log"
  printf '%s\n' 'PASS: Stage4ThetaEnergyTailPointwise'
else
  tail -n 100 "$log"
  printf 'STOP: tail bound build failed; log: %s\n' "$log"
  exit 1
fi
