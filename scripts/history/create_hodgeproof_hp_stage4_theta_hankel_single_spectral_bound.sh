#!/usr/bin/env bash
set -euo pipefail

lake build HodgeProofHP.Stage4ThetaHankelFourthMomentRefinedBound

target="HodgeProofHP/Stage4ThetaHankelSingleSpectralBound.lean"

if [ -f "$target" ]; then
  cp -p "$target" "$target.before_update_$(date +%Y%m%d_%H%M%S)"
fi

cat > "$target" <<'LEAN'
import HodgeProofHP.Stage4ThetaHankelFourthMomentRefinedBound

/-!
Each spectral value supplies a lower bound on the spectral square
energy and hence a necessary fourth-moment bound for scaled equality.
No numerical estimate of a spectral value is assumed here.
-/

noncomputable section

namespace HodgeProofHP

def hpThetaHankelSingleSpectralWeight
    (i : HPThetaHankelSpectralIndex) : ℝ :=
  i.1.re ^ 2 / hpThetaFirstTraceEnergy ^ 2

theorem hpThetaHankelSingleSpectralWeight_mul_energy_sq
    (i : HPThetaHankelSpectralIndex) :
    hpThetaHankelSingleSpectralWeight i *
        hpThetaFirstTraceEnergy ^ 2 =
      i.1.re ^ 2 := by
  unfold hpThetaHankelSingleSpectralWeight
  have hne : hpThetaFirstTraceEnergy ^ 2 ≠ 0 :=
    ne_of_gt hpThetaHankelFirstTraceEnergy_sq_pos
  exact div_mul_cancel₀ (i.1.re ^ 2) hne

theorem hpThetaHankelSingleSpectralWeight_nonneg
    (i : HPThetaHankelSpectralIndex) :
    0 ≤ hpThetaHankelSingleSpectralWeight i := by
  unfold hpThetaHankelSingleSpectralWeight
  exact div_nonneg (sq_nonneg _) (sq_nonneg _)

theorem hpThetaHankelSingleSpectralWeight_le_one
    (i : HPThetaHankelSpectralIndex) :
    hpThetaHankelSingleSpectralWeight i ≤ 1 := by
  have hupper : i.1.re ^ 2 ≤ hpThetaFirstTraceEnergy ^ 2 :=
    le_trans
      (hpThetaHankelSpectralValue_re_sq_le_square_energy i)
      hpThetaHankelSpectralSquareEnergy_le_total_energy_sq
  have hmul := hpThetaHankelSingleSpectralWeight_mul_energy_sq i
  have he := hpThetaHankelFirstTraceEnergy_sq_pos
  by_contra hnot
  have hw : 1 < hpThetaHankelSingleSpectralWeight i :=
    lt_of_not_ge hnot
  have hpos :
      0 < (hpThetaHankelSingleSpectralWeight i - 1) *
        hpThetaFirstTraceEnergy ^ 2 :=
    mul_pos (sub_pos.mpr hw) he
  nlinarith [hpos]

theorem hpThetaHankelScaledSpectralProduct_eq_normalizedXi_single_spectral_bound
    (i : HPThetaHankelSpectralIndex)
    (c : ℝ)
    (hmatch :
      hpThetaHankelScaledSpectralProduct c = hpThetaNormalizedXi) :
    hpThetaPhiMomentFour / (12 * hpThetaPhiMomentZero) ≤
      (1 - hpThetaHankelSingleSpectralWeight i) *
        (hpThetaPhiMomentTwo / (2 * hpThetaPhiMomentZero)) ^ 2 := by
  have hq :
      hpThetaHankelSingleSpectralWeight i *
          hpThetaFirstTraceEnergy ^ 2 ≤
        hpThetaHankelSpectralSquareEnergy := by
    rw [hpThetaHankelSingleSpectralWeight_mul_energy_sq]
    exact hpThetaHankelSpectralValue_re_sq_le_square_energy i
  exact
    hpThetaHankelScaledSpectralProduct_eq_normalizedXi_refined_fourthMoment_bound
      (hpThetaHankelSingleSpectralWeight i) c hq hmatch

theorem hpThetaHankelScaledSpectralProduct_ne_normalizedXi_of_single_spectral_bound
    (i : HPThetaHankelSpectralIndex)
    (hgt :
      (1 - hpThetaHankelSingleSpectralWeight i) *
          (hpThetaPhiMomentTwo / (2 * hpThetaPhiMomentZero)) ^ 2 <
        hpThetaPhiMomentFour / (12 * hpThetaPhiMomentZero))
    (c : ℝ) :
    hpThetaHankelScaledSpectralProduct c ≠ hpThetaNormalizedXi := by
  intro hmatch
  exact (not_le_of_gt hgt)
    (hpThetaHankelScaledSpectralProduct_eq_normalizedXi_single_spectral_bound
      i c hmatch)

#print axioms hpThetaHankelSingleSpectralWeight_mul_energy_sq
#print axioms hpThetaHankelSingleSpectralWeight_nonneg
#print axioms hpThetaHankelSingleSpectralWeight_le_one
#print axioms hpThetaHankelScaledSpectralProduct_eq_normalizedXi_single_spectral_bound
#print axioms hpThetaHankelScaledSpectralProduct_ne_normalizedXi_of_single_spectral_bound

end HodgeProofHP
LEAN

lake env lean "$target"
lake build HodgeProofHP.Stage4ThetaHankelSingleSpectralBound

printf '%s\n' 'PASS: Stage4ThetaHankelSingleSpectralBound'
