#!/usr/bin/env bash
set -euo pipefail

lake build HodgeProofHP.Stage4ThetaHankelSpectralSquareBounds

target="HodgeProofHP/Stage4ThetaHankelFourthMomentNecessaryBound.lean"

if [ -f "$target" ]; then
  cp -p "$target" "$target.before_update_$(date +%Y%m%d_%H%M%S)"
fi

cat > "$target" <<'LEAN'
import HodgeProofHP.Stage4ThetaHankelSpectralSquareBounds

/-!
A necessary upper bound on the normalized fourth theta moment
for equality between a scaled spectral product and normalized Xi.
The strict reverse inequality is not established in this file.
-/

noncomputable section

namespace HodgeProofHP

theorem hpThetaHankelFirstTraceEnergy_sq_pos :
    0 < hpThetaFirstTraceEnergy ^ 2 := by
  have h := hpThetaFirstTraceEnergy_gt_seven_hundredths
  have hE : 0 < hpThetaFirstTraceEnergy := by
    linarith
  exact mul_pos hE hE |> (by simpa only [pow_two] using ·)

private theorem hpTheta_fourthMoment_bound_of_invariant
    (e q r b : ℝ)
    (he : 0 < e ^ 2)
    (hq : 0 ≤ q)
    (h : r ^ 2 * (e ^ 2 - q) = e ^ 2 * b) :
    b ≤ r ^ 2 := by
  have hdiff : e ^ 2 - q ≤ e ^ 2 := by linarith
  have hbound : e ^ 2 * b ≤ e ^ 2 * r ^ 2 := by
    calc
      e ^ 2 * b = r ^ 2 * (e ^ 2 - q) := h.symm
      _ ≤ r ^ 2 * e ^ 2 :=
        mul_le_mul_of_nonneg_left hdiff (sq_nonneg r)
      _ = e ^ 2 * r ^ 2 := by ring
  by_contra hnot
  have hb : r ^ 2 < b := lt_of_not_ge hnot
  have hpos : 0 < e ^ 2 * (b - r ^ 2) :=
    mul_pos he (sub_pos.mpr hb)
  nlinarith [hpos]

theorem hpThetaHankelScaledSpectralProduct_eq_normalizedXi_fourthMoment_bound
    (c : ℝ)
    (hmatch :
      hpThetaHankelScaledSpectralProduct c = hpThetaNormalizedXi) :
    hpThetaPhiMomentFour / (12 * hpThetaPhiMomentZero) ≤
      (hpThetaPhiMomentTwo / (2 * hpThetaPhiMomentZero)) ^ 2 := by
  exact hpTheta_fourthMoment_bound_of_invariant
    hpThetaFirstTraceEnergy
    hpThetaHankelSpectralSquareEnergy
    (hpThetaPhiMomentTwo / (2 * hpThetaPhiMomentZero))
    (hpThetaPhiMomentFour / (12 * hpThetaPhiMomentZero))
    hpThetaHankelFirstTraceEnergy_sq_pos
    hpThetaHankelSpectralSquareEnergy_nonneg
    (hpThetaHankelScaledSpectralProduct_eq_normalizedXi_moment_invariant
      c hmatch)

theorem hpThetaHankelScaledSpectralProduct_ne_normalizedXi_of_fourthMoment_gt
    (hgt :
      (hpThetaPhiMomentTwo / (2 * hpThetaPhiMomentZero)) ^ 2 <
        hpThetaPhiMomentFour / (12 * hpThetaPhiMomentZero))
    (c : ℝ) :
    hpThetaHankelScaledSpectralProduct c ≠ hpThetaNormalizedXi := by
  intro hmatch
  exact (not_le_of_gt hgt)
    (hpThetaHankelScaledSpectralProduct_eq_normalizedXi_fourthMoment_bound
      c hmatch)

#print axioms hpThetaHankelFirstTraceEnergy_sq_pos
#print axioms hpThetaHankelScaledSpectralProduct_eq_normalizedXi_fourthMoment_bound
#print axioms hpThetaHankelScaledSpectralProduct_ne_normalizedXi_of_fourthMoment_gt

end HodgeProofHP
LEAN

lake env lean "$target"
lake build HodgeProofHP.Stage4ThetaHankelFourthMomentNecessaryBound

printf '%s\n' 'PASS: Stage4ThetaHankelFourthMomentNecessaryBound'
