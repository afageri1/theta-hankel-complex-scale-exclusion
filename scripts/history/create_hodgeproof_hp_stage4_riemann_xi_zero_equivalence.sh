#!/usr/bin/env bash
set -euo pipefail

mkdir -p HodgeProofHP

cat > HodgeProofHP/Stage4RiemannXiZeroEquivalence.lean <<'LEAN'
import HodgeProofHP.Stage4RiemannXiDefinition

/-!
# Zero equivalences for the Riemann xi function

Xi has no zero at 0 or 1. Elsewhere its zeros are exactly those of
completed zeta. Transfer to zeta when the Gamma factor is nonzero.
-/

noncomputable section

namespace HodgeProofHP

theorem hpRiemannXi_zero_ne_zero :
    hpRiemannXi 0 ≠ 0 := by
  rw [hpRiemannXi_zero]
  norm_num

theorem hpRiemannXi_one_ne_zero :
    hpRiemannXi 1 ≠ 0 := by
  rw [hpRiemannXi_one]
  norm_num

theorem hpRiemannXi_zero_excludes_endpoints
    (s : ℂ) (hxi : hpRiemannXi s = 0) :
    s ≠ 0 ∧ s ≠ 1 := by
  constructor
  · intro hs
    apply hpRiemannXi_zero_ne_zero
    simpa only [hs] using hxi
  · intro hs
    apply hpRiemannXi_one_ne_zero
    simpa only [hs] using hxi

theorem hpRiemannXi_eq_zero_iff_completed
    (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    hpRiemannXi s = 0 ↔ completedRiemannZeta s = 0 := by
  have hcoeff : s * (s - 1) / 2 ≠ 0 :=
    div_ne_zero
      (mul_ne_zero hs0 (sub_ne_zero.mpr hs1))
      (by norm_num)
  rw [hpRiemannXi_eq_completed s hs0 hs1]
  constructor
  · intro h
    exact (mul_eq_zero.mp h).resolve_left hcoeff
  · intro h
    rw [h, mul_zero]

theorem hpRiemannXi_eq_zero_iff_completed_with_endpoints
    (s : ℂ) :
    hpRiemannXi s = 0 ↔
      s ≠ 0 ∧ s ≠ 1 ∧ completedRiemannZeta s = 0 := by
  constructor
  · intro hxi
    obtain ⟨hs0, hs1⟩ :=
      hpRiemannXi_zero_excludes_endpoints s hxi
    exact ⟨hs0, hs1,
      (hpRiemannXi_eq_zero_iff_completed s hs0 hs1).mp hxi⟩
  · rintro ⟨hs0, hs1, hz⟩
    exact (hpRiemannXi_eq_zero_iff_completed s hs0 hs1).mpr hz

theorem hpRiemannXi_eq_zero_iff_zeta_of_gamma_ne_zero
    (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hgamma : s.Gammaℝ ≠ 0) :
    hpRiemannXi s = 0 ↔ riemannZeta s = 0 := by
  rw [hpRiemannXi_eq_zero_iff_completed s hs0 hs1,
    riemannZeta_def_of_ne_zero hs0]
  constructor
  · intro hz
    rw [hz, zero_div]
  · intro hz
    have h := (div_eq_iff hgamma).mp hz
    simpa only [zero_mul] using h

end HodgeProofHP

#print axioms HodgeProofHP.hpRiemannXi_zero_ne_zero
#print axioms HodgeProofHP.hpRiemannXi_one_ne_zero
#print axioms HodgeProofHP.hpRiemannXi_zero_excludes_endpoints
#print axioms HodgeProofHP.hpRiemannXi_eq_zero_iff_completed
#print axioms HodgeProofHP.hpRiemannXi_eq_zero_iff_completed_with_endpoints
#print axioms HodgeProofHP.hpRiemannXi_eq_zero_iff_zeta_of_gamma_ne_zero
LEAN

lake build HodgeProofHP.Stage4RiemannXiDefinition
lake env lean HodgeProofHP/Stage4RiemannXiZeroEquivalence.lean
lake build HodgeProofHP.Stage4RiemannXiZeroEquivalence
