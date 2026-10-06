#!/usr/bin/env bash
set -euo pipefail

lake build HodgeProofHP.Stage4ThetaTangentTailBound

target="HodgeProofHP/Stage4ThetaProfileSplitUpperBound.lean"

if [ -f "$target" ]; then
  cp -p "$target" "$target.before_update_$(date +%Y%m%d_%H%M%S)"
fi

cat > "$target" <<'LEAN'
import HodgeProofHP.Stage4ThetaTangentTailBound

/-!
Combine a finite tangent-envelope bound with a tail bound.
The resulting explicit expression will be certified numerically
in a subsequent module.
-/

namespace HodgeProofHP

open MeasureTheory

theorem hpThetaProfile_intervalIntegral_le_tangent_difference
    (l p q : ℝ) (hl : 0 ≤ l)
    (hp : 0 ≤ p) (hpq : p ≤ q) :
    (∫ u in p..q, hpRiemannThetaLogProfile u) ≤
      hpThetaProfileTangentTailBound l p -
        hpThetaProfileTangentTailBound l q := by
  have hformula :
      (∫ u in p..q,
        hpThetaGaussianTangentEnvelope Real.pi l u) /
          (1 - Real.exp (-Real.pi)) =
        hpThetaProfileTangentTailBound l p -
          hpThetaProfileTangentTailBound l q := by
    rw [hpThetaGaussianTangentEnvelope_intervalIntegral
      Real.pi l p q
      (ne_of_gt (hpThetaProfileTangent_rate_pos l hl))]
    unfold hpThetaProfileTangentTailBound
    ring
  calc
    (∫ u in p..q, hpRiemannThetaLogProfile u) ≤
        ∫ u in p..q,
          hpThetaGaussianTangentEnvelope Real.pi l u /
            (1 - Real.exp (-Real.pi)) :=
      hpThetaProfile_intervalIntegral_le_tangent l p q hp hpq
    _ = (∫ u in p..q,
          hpThetaGaussianTangentEnvelope Real.pi l u) /
            (1 - Real.exp (-Real.pi)) := by
      rw [intervalIntegral.integral_div]
    _ = hpThetaProfileTangentTailBound l p -
        hpThetaProfileTangentTailBound l q := hformula

noncomputable def hpThetaProfileSplitUpperBound
    (l p : ℝ) : ℝ :=
  hpThetaProfileTangentTailBound l 0 -
    hpThetaProfileTangentTailBound l p +
    hpThetaProfileTangentTailBound p p

theorem hpThetaProfile_integral_le_split_upper
    (l p : ℝ) (hl : 0 ≤ l) (hp : 0 ≤ p) :
    (∫ u in Set.Ioi 0, hpRiemannThetaLogProfile u) ≤
      hpThetaProfileSplitUpperBound l p := by
  have hsplit :
      (∫ u in (0 : ℝ)..p, hpRiemannThetaLogProfile u) +
        (∫ u in Set.Ioi p, hpRiemannThetaLogProfile u) =
          ∫ u in Set.Ioi 0, hpRiemannThetaLogProfile u :=
    intervalIntegral.integral_interval_add_Ioi
      (hpThetaProfile_integrableOn_tail 0 (by norm_num))
      (hpThetaProfile_integrableOn_tail p hp)
  have hfinite :=
    hpThetaProfile_intervalIntegral_le_tangent_difference
      l 0 p hl (by norm_num) hp
  have htail :=
    hpThetaProfile_tail_integral_le_tangent p p hp hp
  calc
    (∫ u in Set.Ioi 0, hpRiemannThetaLogProfile u) =
        (∫ u in (0 : ℝ)..p, hpRiemannThetaLogProfile u) +
          (∫ u in Set.Ioi p, hpRiemannThetaLogProfile u) :=
      hsplit.symm
    _ ≤ hpThetaProfileSplitUpperBound l p := by
      unfold hpThetaProfileSplitUpperBound
      exact add_le_add hfinite htail

noncomputable def hpThetaProfileTwoTenthsUpperBound : ℝ :=
  hpThetaProfileSplitUpperBound (1 / 10) (1 / 5)

theorem hpThetaProfile_integral_le_twoTenths_upper :
    (∫ u in Set.Ioi 0, hpRiemannThetaLogProfile u) ≤
      hpThetaProfileTwoTenthsUpperBound := by
  exact hpThetaProfile_integral_le_split_upper
    (1 / 10) (1 / 5) (by norm_num) (by norm_num)

theorem hpThetaPhiMomentTwo_le_twoTenths_upper :
    hpThetaPhiMomentTwo ≤
      2 * hpThetaProfileTwoTenthsUpperBound := by
  calc
    hpThetaPhiMomentTwo ≤
        2 * (∫ u in Set.Ioi 0, hpRiemannThetaLogProfile u) :=
      hpThetaPhiMomentTwo_le_twice_profile_integral
    _ ≤ 2 * hpThetaProfileTwoTenthsUpperBound :=
      mul_le_mul_of_nonneg_left
        hpThetaProfile_integral_le_twoTenths_upper
        (by norm_num : (0 : ℝ) ≤ 2)

#print axioms hpThetaProfile_intervalIntegral_le_tangent_difference
#print axioms hpThetaProfile_integral_le_split_upper
#print axioms hpThetaProfile_integral_le_twoTenths_upper
#print axioms hpThetaPhiMomentTwo_le_twoTenths_upper

end HodgeProofHP
LEAN

lake env lean "$target"
lake build HodgeProofHP.Stage4ThetaProfileSplitUpperBound

printf '%s\n' 'PASS: Stage4ThetaProfileSplitUpperBound'
