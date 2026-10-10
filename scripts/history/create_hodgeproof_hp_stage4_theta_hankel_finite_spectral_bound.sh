#!/usr/bin/env bash
set -euo pipefail

lake build HodgeProofHP.Stage4ThetaHankelSingleSpectralBound

target="HodgeProofHP/Stage4ThetaHankelFiniteSpectralBound.lean"

if [ -f "$target" ]; then
  cp -p "$target" "$target.before_update_$(date +%Y%m%d_%H%M%S)"
fi

cat > "$target" <<'LEAN'
import HodgeProofHP.Stage4ThetaHankelSingleSpectralBound
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
Finite collections of spectral values give lower bounds on the
spectral square energy and necessary fourth-moment bounds for
scaled equality with normalized Xi.
-/

noncomputable section

namespace HodgeProofHP

def hpThetaHankelFiniteSpectralWeight
    (F : Finset HPThetaHankelSpectralIndex) : ℝ :=
  (∑ i ∈ F, i.1.re ^ 2) / hpThetaFirstTraceEnergy ^ 2

theorem hpThetaHankelFiniteSpectralSquares_le_square_energy
    (F : Finset HPThetaHankelSpectralIndex) :
    (∑ i ∈ F, i.1.re ^ 2) ≤ hpThetaHankelSpectralSquareEnergy := by
  have hs := hpThetaHankelSpectralSquares_real_hasSum
  calc
    (∑ i ∈ F, i.1.re ^ 2) ≤
        ∑' i : HPThetaHankelSpectralIndex, i.1.re ^ 2 :=
      Summable.sum_le_tsum F (fun i _ => sq_nonneg i.1.re)
        hs.summable
    _ = hpThetaHankelSpectralSquareEnergy := hs.tsum_eq

theorem hpThetaHankelFiniteSpectralWeight_mul_energy_sq
    (F : Finset HPThetaHankelSpectralIndex) :
    hpThetaHankelFiniteSpectralWeight F *
        hpThetaFirstTraceEnergy ^ 2 =
      ∑ i ∈ F, i.1.re ^ 2 := by
  unfold hpThetaHankelFiniteSpectralWeight
  exact div_mul_cancel₀ _
    (ne_of_gt hpThetaHankelFirstTraceEnergy_sq_pos)

theorem hpThetaHankelFiniteSpectralWeight_nonneg
    (F : Finset HPThetaHankelSpectralIndex) :
    0 ≤ hpThetaHankelFiniteSpectralWeight F := by
  unfold hpThetaHankelFiniteSpectralWeight
  exact div_nonneg
    (Finset.sum_nonneg (fun i _ => sq_nonneg i.1.re))
    (sq_nonneg _)

theorem hpThetaHankelFiniteSpectralWeight_le_one
    (F : Finset HPThetaHankelSpectralIndex) :
    hpThetaHankelFiniteSpectralWeight F ≤ 1 := by
  have hupper :
      (∑ i ∈ F, i.1.re ^ 2) ≤ hpThetaFirstTraceEnergy ^ 2 :=
    le_trans
      (hpThetaHankelFiniteSpectralSquares_le_square_energy F)
      hpThetaHankelSpectralSquareEnergy_le_total_energy_sq
  have hmul := hpThetaHankelFiniteSpectralWeight_mul_energy_sq F
  have he := hpThetaHankelFirstTraceEnergy_sq_pos
  by_contra hnot
  have hw : 1 < hpThetaHankelFiniteSpectralWeight F :=
    lt_of_not_ge hnot
  have hpos :
      0 < (hpThetaHankelFiniteSpectralWeight F - 1) *
        hpThetaFirstTraceEnergy ^ 2 :=
    mul_pos (sub_pos.mpr hw) he
  nlinarith [hpos]

theorem hpThetaHankelScaledSpectralProduct_eq_normalizedXi_finite_spectral_bound
    (F : Finset HPThetaHankelSpectralIndex)
    (c : ℝ)
    (hmatch :
      hpThetaHankelScaledSpectralProduct c = hpThetaNormalizedXi) :
    hpThetaPhiMomentFour / (12 * hpThetaPhiMomentZero) ≤
      (1 - hpThetaHankelFiniteSpectralWeight F) *
        (hpThetaPhiMomentTwo / (2 * hpThetaPhiMomentZero)) ^ 2 := by
  have hq :
      hpThetaHankelFiniteSpectralWeight F *
          hpThetaFirstTraceEnergy ^ 2 ≤
        hpThetaHankelSpectralSquareEnergy := by
    rw [hpThetaHankelFiniteSpectralWeight_mul_energy_sq]
    exact hpThetaHankelFiniteSpectralSquares_le_square_energy F
  exact
    hpThetaHankelScaledSpectralProduct_eq_normalizedXi_refined_fourthMoment_bound
      (hpThetaHankelFiniteSpectralWeight F) c hq hmatch

theorem hpThetaHankelScaledSpectralProduct_ne_normalizedXi_of_finite_spectral_bound
    (F : Finset HPThetaHankelSpectralIndex)
    (hgt :
      (1 - hpThetaHankelFiniteSpectralWeight F) *
          (hpThetaPhiMomentTwo / (2 * hpThetaPhiMomentZero)) ^ 2 <
        hpThetaPhiMomentFour / (12 * hpThetaPhiMomentZero))
    (c : ℝ) :
    hpThetaHankelScaledSpectralProduct c ≠ hpThetaNormalizedXi := by
  intro hmatch
  exact (not_le_of_gt hgt)
    (hpThetaHankelScaledSpectralProduct_eq_normalizedXi_finite_spectral_bound
      F c hmatch)

#print axioms hpThetaHankelFiniteSpectralSquares_le_square_energy
#print axioms hpThetaHankelFiniteSpectralWeight_mul_energy_sq
#print axioms hpThetaHankelFiniteSpectralWeight_nonneg
#print axioms hpThetaHankelFiniteSpectralWeight_le_one
#print axioms hpThetaHankelScaledSpectralProduct_eq_normalizedXi_finite_spectral_bound
#print axioms hpThetaHankelScaledSpectralProduct_ne_normalizedXi_of_finite_spectral_bound

end HodgeProofHP
LEAN

lake env lean "$target"
lake build HodgeProofHP.Stage4ThetaHankelFiniteSpectralBound

printf '%s\n' 'PASS: Stage4ThetaHankelFiniteSpectralBound'
