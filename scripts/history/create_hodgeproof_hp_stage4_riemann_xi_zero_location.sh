#!/usr/bin/env bash
set -euo pipefail

mkdir -p HodgeProofHP

cat > HodgeProofHP/Stage4RiemannXiZeroLocation.lean <<'LEAN'
import HodgeProofHP.Stage4RiemannXiCriticalStrip
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# All xi zeros lie in the open critical strip

Use zeta nonvanishing on Re(s) >= 1 and the xi functional equation.
This proves location in the strip, not location on its central line.
-/

noncomputable section

namespace HodgeProofHP

theorem hpRiemannXi_ne_zero_of_one_le_re
    (s : ℂ) (hs : 1 ≤ s.re) :
    hpRiemannXi s ≠ 0 := by
  intro hxi
  have hs1 := (hpRiemannXi_zero_excludes_endpoints s hxi).2
  have hpos : 0 < s.re := by
    linarith
  have hz : riemannZeta s = 0 :=
    (hpRiemannXi_eq_zero_iff_zeta_of_re_pos s hpos hs1).mp hxi
  exact (riemannZeta_ne_zero_of_one_le_re hs) hz

theorem hpRiemannXi_ne_zero_of_re_nonpos
    (s : ℂ) (hs : s.re ≤ 0) :
    hpRiemannXi s ≠ 0 := by
  have hright : 1 ≤ (1 - s).re := by
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  intro hxi
  apply hpRiemannXi_ne_zero_of_one_le_re (1 - s) hright
  rw [hpRiemannXi_one_sub]
  exact hxi

theorem hpRiemannXi_zero_mem_critical_strip
    (s : ℂ) (hxi : hpRiemannXi s = 0) :
    0 < s.re ∧ s.re < 1 := by
  constructor
  · by_contra h
    have hs : s.re ≤ 0 := le_of_not_gt h
    exact hpRiemannXi_ne_zero_of_re_nonpos s hs hxi
  · by_contra h
    have hs : 1 ≤ s.re := le_of_not_gt h
    exact hpRiemannXi_ne_zero_of_one_le_re s hs hxi

theorem hpRiemannXi_eq_zero_iff_zeta_and_critical_strip
    (s : ℂ) :
    hpRiemannXi s = 0 ↔
      riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 := by
  constructor
  · intro hxi
    obtain ⟨hpos, hlt⟩ := hpRiemannXi_zero_mem_critical_strip s hxi
    exact ⟨
      (hpRiemannXi_eq_zero_iff_zeta_in_critical_strip s hpos hlt).mp hxi,
      hpos, hlt⟩
  · rintro ⟨hz, hpos, hlt⟩
    exact
      (hpRiemannXi_eq_zero_iff_zeta_in_critical_strip s hpos hlt).mpr hz

end HodgeProofHP

#print axioms HodgeProofHP.hpRiemannXi_ne_zero_of_one_le_re
#print axioms HodgeProofHP.hpRiemannXi_ne_zero_of_re_nonpos
#print axioms HodgeProofHP.hpRiemannXi_zero_mem_critical_strip
#print axioms HodgeProofHP.hpRiemannXi_eq_zero_iff_zeta_and_critical_strip
LEAN

lake build HodgeProofHP.Stage4RiemannXiCriticalStrip
lake build Mathlib.NumberTheory.LSeries.Nonvanishing
lake env lean HodgeProofHP/Stage4RiemannXiZeroLocation.lean
lake build HodgeProofHP.Stage4RiemannXiZeroLocation
