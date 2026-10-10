#!/usr/bin/env bash
set -euo pipefail

lake env lean HodgeProofHP/Stage3GaussianExponentialBound.lean
lake build HodgeProofHP.Stage3GaussianExponentialBound

target="HodgeProofHP/Stage3GaussianExponentialIntegrability.lean"

if [ -f "$target" ]; then
  cp "$target" "${target}.before_exponential_integrability"
fi

cat > "$target" <<'LEAN'
import HodgeProofHP.Stage3GaussianExponentialBound
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! Exponential Gaussian weights in L2 and their products with L2 norms. -/

open MeasureTheory

namespace HodgeProofHP

theorem hpQuarterGaussian_memLp :
    MemLp (fun x : ℝ => Real.exp (-(x ^ 2 / 4))) 2 volume := by
  have hcont :
      Continuous (fun x : ℝ => Real.exp (-(x ^ 2 / 4))) := by
    fun_prop
  apply (memLp_two_iff_integrable_sq
    hcont.aestronglyMeasurable).2
  have hbase :
      Integrable (fun x : ℝ => Real.exp (-(1 / 2 : ℝ) * x ^ 2))
        volume :=
    integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)
  have heq :
      (fun x : ℝ => Real.exp (-(x ^ 2 / 4)) ^ 2) =
        (fun x : ℝ => Real.exp (-(1 / 2 : ℝ) * x ^ 2)) := by
    funext x
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [heq]
  exact hbase

theorem hpGaussianExponentialWeight_memLp (a : ℝ) :
    MemLp
      (fun x : ℝ =>
        Real.exp (a * |x|) * Real.exp (-(x ^ 2 / 2)))
      2 volume := by
  have hmajor :
      MemLp
        (fun x : ℝ =>
          Real.exp (a ^ 2) * Real.exp (-(x ^ 2 / 4)))
        2 volume := by
    have h :=
      hpQuarterGaussian_memLp.const_smul (Real.exp (a ^ 2))
    change MemLp
      (fun x : ℝ =>
        Real.exp (a ^ 2) * Real.exp (-(x ^ 2 / 4)))
      2 volume at h
    exact h
  have hcont :
      Continuous
        (fun x : ℝ =>
          Real.exp (a * |x|) * Real.exp (-(x ^ 2 / 2))) := by
    fun_prop
  apply hmajor.mono' hcont.aestronglyMeasurable
  filter_upwards with x
  rw [Real.norm_eq_abs,
    abs_of_pos (mul_pos (Real.exp_pos _) (Real.exp_pos _))]
  exact hpGaussian_exponential_weight_bound a x

theorem hpGaussianExponentialWeight_mul_L2_norm_integrable
    (a : ℝ) (v : HPSpace) :
    Integrable
      (fun x : ℝ =>
        (Real.exp (a * |x|) * Real.exp (-(x ^ 2 / 2))) *
          ‖v x‖)
      volume := by
  exact (hpGaussianExponentialWeight_memLp a).integrable_mul
    (MeasureTheory.Lp.memLp v).norm

#print axioms hpQuarterGaussian_memLp
#print axioms hpGaussianExponentialWeight_memLp
#print axioms hpGaussianExponentialWeight_mul_L2_norm_integrable

end HodgeProofHP
LEAN

lake env lean "$target"
lake build HodgeProofHP.Stage3GaussianExponentialIntegrability
