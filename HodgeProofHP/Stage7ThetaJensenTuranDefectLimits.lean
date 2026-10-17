/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenTuranDefectUpper

/-!
# Actual Turan defect limits and the remaining step condition

The unconditional defect upper bound implies u_n -> 0 and
1/u_n -> infinity. The adjacent normalized coefficient ratio tends to one.
None of these limits controls adjacent reciprocal differences.

The squared step condition is exactly equivalent to
|1/u_n - 1/u_(n+1)| <= 3. A rational counterexample records that
positive quarter bounds alone do not imply this condition.
No lower asymptotic equivalent for u_n is assumed or proved.
-/

noncomputable section
open Filter
open scoped Topology
namespace HodgeProofHP

theorem hpThetaJensenTuranDefect_tendsto_zero :
    Tendsto hpThetaJensenTuranDefect atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Filter.Eventually.of_forall
      (fun n => ha.trans (hpThetaJensenTuranDefect_pos n))
  · intro b hb
    obtain ⟨N, hN⟩ := exists_nat_gt (2 / b)
    apply eventually_atTop.mpr
    refine ⟨N, ?_⟩
    intro n hn
    have hn' : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hNb : 2 < (N : ℝ) * b := (div_lt_iff₀ hb).mp hN
    apply (hpThetaJensenTuranDefect_le_reciprocal n).trans_lt
    apply (div_lt_iff₀ (by positivity : 0 < 2 * (n : ℝ) + 3)).mpr
    have hmul := mul_le_mul_of_nonneg_right hn' hb.le
    nlinarith [hmul]

theorem hpThetaJensenTuranDefect_inv_ge_linear (n : ℕ) :
    (2 * (n : ℝ) + 3) / 2 ≤ 1 / hpThetaJensenTuranDefect n := by
  have h := (le_div_iff₀ (by positivity : 0 < 2 * (n : ℝ) + 3)).mp
    (hpThetaJensenTuranDefect_le_reciprocal n)
  apply (le_div_iff₀ (hpThetaJensenTuranDefect_pos n)).mpr
  nlinarith only [h]

theorem hpThetaJensenTuranDefect_inv_tendsto_atTop :
    Tendsto (fun n => 1 / hpThetaJensenTuranDefect n) atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  obtain ⟨N, hN⟩ := exists_nat_gt b
  apply eventually_atTop.mpr
  refine ⟨N, ?_⟩
  intro n hn
  have hn' : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  calc
    b ≤ (n : ℝ) := by linarith
    _ ≤ (2 * (n : ℝ) + 3) / 2 := by linarith
    _ ≤ 1 / hpThetaJensenTuranDefect n :=
      hpThetaJensenTuranDefect_inv_ge_linear n

theorem hpThetaJensenGamma_ratio_eq_one_sub_defect (n : ℕ) :
    hpThetaJensenGamma n * hpThetaJensenGamma (n + 2) /
      hpThetaJensenGamma (n + 1) ^ 2 = 1 - hpThetaJensenTuranDefect n := by
  have hb := (hpThetaJensenGamma_pos_allShifts (n + 1)).ne'
  unfold hpThetaJensenTuranDefect hpThetaJensenTuranGap
  field_simp [hb] <;> ring

theorem hpThetaJensenGamma_adjacent_ratio_tendsto_one :
    Tendsto (fun n => hpThetaJensenGamma n * hpThetaJensenGamma (n + 2) /
      hpThetaJensenGamma (n + 1) ^ 2) atTop (𝓝 1) := by
  simp_rw [hpThetaJensenGamma_ratio_eq_one_sub_defect]
  simpa only [sub_zero] using
    (tendsto_const_nhds.sub hpThetaJensenTuranDefect_tendsto_zero)

theorem hpPositiveDefect_squared_step_iff_inv_step (u v : ℝ)
    (hu : 0 < u) (hv : 0 < v) :
    (u - v) ^ 2 ≤ 9 * u ^ 2 * v ^ 2 ↔ |1 / u - 1 / v| ≤ 3 := by
  have hp := mul_pos hu hv
  have he : |1 / u - 1 / v| = |u - v| / (u * v) := by
    have h : 1 / u - 1 / v = -(u - v) / (u * v) := by
      field_simp [hu.ne', hv.ne'] <;> ring
    rw [h, abs_div, abs_neg, abs_of_pos hp]
  rw [he, div_le_iff₀ hp]
  have h3 : 0 ≤ 3 * (u * v) := by positivity
  have habs := sq_abs (u - v)
  constructor
  · intro h
    apply (sq_le_sq₀ (abs_nonneg (u - v)) h3).mp
    nlinarith only [h, habs]
  · intro h
    have hs := (sq_le_sq₀ (abs_nonneg (u - v)) h3).mpr h
    nlinarith only [hs, habs]

theorem hpThetaJensenTuranDefect_step_iff_inv_step (n : ℕ) :
    (hpThetaJensenTuranDefect n - hpThetaJensenTuranDefect (n + 1)) ^ 2 ≤
      9 * hpThetaJensenTuranDefect n ^ 2 * hpThetaJensenTuranDefect (n + 1) ^ 2 ↔
    |1 / hpThetaJensenTuranDefect n - 1 / hpThetaJensenTuranDefect (n + 1)| ≤ 3 :=
  hpPositiveDefect_squared_step_iff_inv_step _ _
    (hpThetaJensenTuranDefect_pos n) (hpThetaJensenTuranDefect_pos (n + 1))

theorem hpPositiveDefect_quarter_bounds_not_sufficient :
    ∃ u v : ℝ, 0 < u ∧ 0 < v ∧ u ≤ 1 / 4 ∧ v ≤ 1 / 4 ∧
      ¬ ((u - v) ^ 2 ≤ 9 * u ^ 2 * v ^ 2) := by
  refine ⟨1 / 4, 1 / 1000, ?_⟩
  norm_num

#print axioms hpThetaJensenTuranDefect_tendsto_zero
#print axioms hpThetaJensenTuranDefect_inv_ge_linear
#print axioms hpThetaJensenTuranDefect_inv_tendsto_atTop
#print axioms hpThetaJensenGamma_ratio_eq_one_sub_defect
#print axioms hpThetaJensenGamma_adjacent_ratio_tendsto_one
#print axioms hpPositiveDefect_squared_step_iff_inv_step
#print axioms hpThetaJensenTuranDefect_step_iff_inv_step
#print axioms hpPositiveDefect_quarter_bounds_not_sufficient
end HodgeProofHP
