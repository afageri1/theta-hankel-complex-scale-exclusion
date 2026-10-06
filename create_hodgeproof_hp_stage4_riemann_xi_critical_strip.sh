#!/usr/bin/env bash
set -euo pipefail

mkdir -p HodgeProofHP

cat > HodgeProofHP/Stage4RiemannXiCriticalStrip.lean <<'LEAN'
import HodgeProofHP.Stage4RiemannXiZeroEquivalence
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Tactic.Linarith

/-!
# Xi and zeta zeros in the critical strip

Remove the explicit Gamma nonvanishing hypothesis when Re(s) > 0.
Specialize to the open critical strip and to real critical-line
coordinates. No assertion that all zeros lie on the line is made.
-/

noncomputable section

namespace HodgeProofHP

theorem hpRiemannXi_eq_zero_iff_zeta_of_re_pos
    (s : ℂ) (hpos : 0 < s.re) (hs1 : s ≠ 1) :
    hpRiemannXi s = 0 ↔ riemannZeta s = 0 := by
  have hs0 : s ≠ 0 := by
    intro hs
    have hre := congrArg Complex.re hs
    simp only [Complex.zero_re] at hre
    linarith
  exact hpRiemannXi_eq_zero_iff_zeta_of_gamma_ne_zero
    s hs0 hs1 (Complex.Gammaℝ_ne_zero_of_re_pos hpos)

theorem hpRiemannXi_eq_zero_iff_zeta_in_critical_strip
    (s : ℂ) (hpos : 0 < s.re) (hlt : s.re < 1) :
    hpRiemannXi s = 0 ↔ riemannZeta s = 0 := by
  have hs1 : s ≠ 1 := by
    intro hs
    have hre := congrArg Complex.re hs
    simp only [Complex.one_re] at hre
    linarith
  exact hpRiemannXi_eq_zero_iff_zeta_of_re_pos s hpos hs1

theorem hpRiemannXiCritical_eq_zero_iff_zeta_real
    (t : ℝ) :
    hpRiemannXiCritical (t : ℂ) = 0 ↔
      riemannZeta ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) = 0 := by
  have hre :
      ((1 / 2 : ℂ) + Complex.I * (t : ℂ)).re = (1 / 2 : ℝ) := by
    norm_num [Complex.mul_re]
  have hpos :
      0 < ((1 / 2 : ℂ) + Complex.I * (t : ℂ)).re := by
    rw [hre]
    norm_num
  have hlt :
      ((1 / 2 : ℂ) + Complex.I * (t : ℂ)).re < 1 := by
    rw [hre]
    norm_num
  change
    hpRiemannXi ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) = 0 ↔ _
  exact hpRiemannXi_eq_zero_iff_zeta_in_critical_strip
    ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) hpos hlt

theorem hpRiemannXiCritical_real_zero_neg_iff
    (t : ℝ) :
    hpRiemannXiCritical ((-t : ℝ) : ℂ) = 0 ↔
      hpRiemannXiCritical (t : ℂ) = 0 := by
  rw [Complex.ofReal_neg, hpRiemannXiCritical_even]

end HodgeProofHP

#print axioms HodgeProofHP.hpRiemannXi_eq_zero_iff_zeta_of_re_pos
#print axioms HodgeProofHP.hpRiemannXi_eq_zero_iff_zeta_in_critical_strip
#print axioms HodgeProofHP.hpRiemannXiCritical_eq_zero_iff_zeta_real
#print axioms HodgeProofHP.hpRiemannXiCritical_real_zero_neg_iff
LEAN

lake build HodgeProofHP.Stage4RiemannXiZeroEquivalence
lake env lean HodgeProofHP/Stage4RiemannXiCriticalStrip.lean
lake build HodgeProofHP.Stage4RiemannXiCriticalStrip
