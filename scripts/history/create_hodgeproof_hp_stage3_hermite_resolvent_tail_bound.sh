#!/usr/bin/env bash
set -euo pipefail

mkdir -p HodgeProofHP

cat > HodgeProofHP/Stage3HermiteResolventTailBound.lean <<'LEAN'
import HodgeProofHP.Stage3HermiteFiniteApproximationCompact
import Mathlib.Analysis.Normed.Lp.lpSpace

/-!
# Operator-norm bound for the finite Hermite resolvent error

Discarded coefficients have indices at least N.
Their resolvent denominators have norm at least 2N + 1.
-/

noncomputable section

namespace HodgeProofHP

theorem hpHermiteCoefficient_finiteProjection
    (N : ℕ) (v : HPSpace) (n : ℕ) :
    hpHermiteCoefficient (hpHermiteFiniteProjection N v) n =
      if n < N then hpHermiteCoefficient v n else 0 := by
  rw [hpHermiteFiniteProjection_apply]
  change
    inner ℂ (hpHermiteNormalizedL2 n)
        (∑ m ∈ Finset.range N,
          hpHermiteCoefficient v m • hpHermiteNormalizedL2 m) =
      if n < N then hpHermiteCoefficient v n else 0
  by_cases hn : n < N
  · simp only [hn, ite_true]
    exact hpHermiteNormalizedL2_orthonormal.inner_right_sum
      (hpHermiteCoefficient v) (Finset.mem_range.mpr hn)
  · simp only [hn, ite_false]
    change
      ((innerSL ℂ) (hpHermiteNormalizedL2 n))
        (∑ m ∈ Finset.range N,
          hpHermiteCoefficient v m • hpHermiteNormalizedL2 m) = 0
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro m hm
    have hmN : m < N := Finset.mem_range.mp hm
    have hnm : n ≠ m := by omega
    change
      inner ℂ (hpHermiteNormalizedL2 n)
        (hpHermiteCoefficient v m • hpHermiteNormalizedL2 m) = 0
    rw [inner_smul_right,
      hpHermiteNormalizedL2_orthogonal_of_ne n m hnm,
      mul_zero]

theorem hpHermiteResolvent_denominator_norm_lower
    (c : ℂ) (hcRe : c.re = 0) (n : ℕ) :
    2 * (n : ℝ) + 1 ≤
      ‖(2 * (n : ℂ) + 1) - (starRingEnd ℂ) c‖ := by
  simpa [Complex.mul_re, hcRe] using
    Complex.re_le_norm
      ((2 * (n : ℂ) + 1) - (starRingEnd ℂ) c)

theorem hpHermiteResolvent_tail_coefficient_bound
    (c : ℂ) (hcRe : c.re = 0)
    (N n : ℕ) (hNn : N ≤ n) (a : ℂ) :
    ‖a / ((2 * (n : ℂ) + 1) - (starRingEnd ℂ) c)‖ ≤
      (2 * (N : ℝ) + 1)⁻¹ * ‖a‖ := by
  have hpos : 0 < 2 * (N : ℝ) + 1 := by positivity
  have hcast : (N : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hNn
  have hbase := hpHermiteResolvent_denominator_norm_lower c hcRe n
  have hden :
      2 * (N : ℝ) + 1 ≤
        ‖(2 * (n : ℂ) + 1) - (starRingEnd ℂ) c‖ := by
    linarith
  rw [norm_div]
  calc
    ‖a‖ / ‖(2 * (n : ℂ) + 1) - (starRingEnd ℂ) c‖ ≤
        ‖a‖ / (2 * (N : ℝ) + 1) :=
      div_le_div_of_nonneg_left (norm_nonneg a) hpos hden
    _ = (2 * (N : ℝ) + 1)⁻¹ * ‖a‖ := by
      rw [div_eq_mul_inv, mul_comm]

theorem hpHermiteFiniteResolventApproximation_error_norm_le
    (c : ℂ) (hcIm : c.im ≠ 0) (hcRe : c.re = 0)
    (hcNorm : ‖c‖ = 1) (N : ℕ) (v : HPSpace) :
    ‖hpHarmonicUnitImaginaryResolvent c hcIm hcRe hcNorm v -
        hpHermiteFiniteResolventApproximation c hcIm hcRe hcNorm N v‖ ≤
      (2 * (N : ℝ) + 1)⁻¹ * ‖v‖ := by
  let K : ℝ := (2 * (N : ℝ) + 1)⁻¹
  let w : HPSpace :=
    hpHarmonicUnitImaginaryResolvent c hcIm hcRe hcNorm v
  let e : HPSpace :=
    w - hpHermiteFiniteProjection N w
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  have hpoint :
      ∀ n, ‖hpHermiteCoefficient e n‖ ≤
        K * ‖hpHermiteCoefficient v n‖ := by
    intro n
    have heq :
        hpHermiteCoefficient e n =
          hpHermiteCoefficient w n -
            hpHermiteCoefficient (hpHermiteFiniteProjection N w) n := by
      change
        inner ℂ (hpHermiteNormalizedL2 n)
            (w - hpHermiteFiniteProjection N w) =
          inner ℂ (hpHermiteNormalizedL2 n) w -
            inner ℂ (hpHermiteNormalizedL2 n)
              (hpHermiteFiniteProjection N w)
      exact inner_sub_right _ _ _
    rw [heq, hpHermiteCoefficient_finiteProjection]
    by_cases hn : n < N
    · simp only [hn, ite_true, sub_self, norm_zero]
      exact mul_nonneg hK (norm_nonneg _)
    · simp only [hn, ite_false, sub_zero]
      change
        ‖hpHermiteCoefficient
          (hpHarmonicUnitImaginaryResolvent c hcIm hcRe hcNorm v) n‖ ≤
          (2 * (N : ℝ) + 1)⁻¹ * ‖hpHermiteCoefficient v n‖
      rw [hpHermiteCoefficient_unitImaginaryResolvent]
      exact hpHermiteResolvent_tail_coefficient_bound c hcRe N n
        (Nat.le_of_not_gt hn) (hpHermiteCoefficient v n)
  have hmono :
      ‖hpHermiteCoordinateEquiv e‖ ≤
        ‖(K : ℂ) • hpHermiteCoordinateEquiv v‖ := by
    apply lp.norm_mono (p := (2 : ENNReal)) (by norm_num)
    intro n
    change
      ‖hpHermiteCoordinateEquiv e n‖ ≤
        ‖(K : ℂ) * hpHermiteCoordinateEquiv v n‖
    simp only [hpHermiteCoordinateEquiv_apply, norm_mul,
      Complex.norm_of_nonneg hK]
    exact hpoint n
  have hnorm : ‖e‖ ≤ K * ‖v‖ := by
    calc
      ‖e‖ = ‖hpHermiteCoordinateEquiv e‖ :=
        (hpHermiteCoordinateEquiv.norm_map e).symm
      _ ≤ ‖(K : ℂ) • hpHermiteCoordinateEquiv v‖ := hmono
      _ = K * ‖v‖ := by
        rw [norm_smul, Complex.norm_of_nonneg hK,
          hpHermiteCoordinateEquiv.norm_map]
  simpa only [e, w, K, hpHermiteFiniteResolventApproximation,
    ContinuousLinearMap.comp_apply] using hnorm

theorem hpHermiteFiniteResolventApproximation_error_opNorm_le
    (c : ℂ) (hcIm : c.im ≠ 0) (hcRe : c.re = 0)
    (hcNorm : ‖c‖ = 1) (N : ℕ) :
    ‖hpHarmonicUnitImaginaryResolvent c hcIm hcRe hcNorm -
        hpHermiteFiniteResolventApproximation c hcIm hcRe hcNorm N‖ ≤
      (2 * (N : ℝ) + 1)⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  change
    ‖hpHarmonicUnitImaginaryResolvent c hcIm hcRe hcNorm v -
        hpHermiteFiniteResolventApproximation c hcIm hcRe hcNorm N v‖ ≤
      (2 * (N : ℝ) + 1)⁻¹ * ‖v‖
  exact hpHermiteFiniteResolventApproximation_error_norm_le
    c hcIm hcRe hcNorm N v

end HodgeProofHP

#print axioms HodgeProofHP.hpHermiteCoefficient_finiteProjection
#print axioms HodgeProofHP.hpHermiteResolvent_denominator_norm_lower
#print axioms HodgeProofHP.hpHermiteResolvent_tail_coefficient_bound
#print axioms HodgeProofHP.hpHermiteFiniteResolventApproximation_error_norm_le
#print axioms HodgeProofHP.hpHermiteFiniteResolventApproximation_error_opNorm_le
LEAN

lake build HodgeProofHP.Stage3HermiteFiniteApproximationCompact
lake env lean HodgeProofHP/Stage3HermiteResolventTailBound.lean
lake build HodgeProofHP.Stage3HermiteResolventTailBound
