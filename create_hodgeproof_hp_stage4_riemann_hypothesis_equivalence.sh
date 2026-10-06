#!/usr/bin/env bash
set -euo pipefail

mkdir -p HodgeProofHP

cat > HodgeProofHP/Stage4RiemannHypothesisEquivalence.lean <<'LEAN'
import HodgeProofHP.Stage4RiemannXiRealZeroCriterion
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Riemann hypothesis and real zeros of the critical xi function

These results prove equivalent formulations.
They do not prove the Riemann hypothesis.
-/

noncomputable section

namespace HodgeProofHP

theorem hpRiemannZeta_zero_ne_zero
    (s : ℂ) (hz : riemannZeta s = 0) :
    s ≠ 0 := by
  intro hs
  subst s
  rw [riemannZeta_zero] at hz
  norm_num at hz

theorem hpRiemannZeta_nontrivial_zero_gamma_ne_zero
    (s : ℂ)
    (hz : riemannZeta s = 0)
    (hnt : ¬ ∃ n : ℕ, s = -2 * ((n : ℂ) + 1)) :
    s.Gammaℝ ≠ 0 := by
  intro hg
  obtain ⟨n, hn⟩ := Complex.Gammaℝ_eq_zero_iff.mp hg
  cases n with
  | zero =>
      apply hpRiemannZeta_zero_ne_zero s hz
      simpa using hn
  | succ n =>
      apply hnt
      refine ⟨n, ?_⟩
      calc
        s = -(2 * ((Nat.succ n : ℕ) : ℂ)) := hn
        _ = -2 * ((n : ℂ) + 1) := by
          rw [Nat.cast_succ]
          ring

theorem hpRiemannXi_eq_zero_of_nontrivial_zeta_zero
    (s : ℂ)
    (hz : riemannZeta s = 0)
    (hnt : ¬ ∃ n : ℕ, s = -2 * ((n : ℂ) + 1))
    (hs1 : s ≠ 1) :
    hpRiemannXi s = 0 := by
  have hs0 : s ≠ 0 := hpRiemannZeta_zero_ne_zero s hz
  have hg : s.Gammaℝ ≠ 0 :=
    hpRiemannZeta_nontrivial_zero_gamma_ne_zero s hz hnt
  exact
    (hpRiemannXi_eq_zero_iff_zeta_of_gamma_ne_zero
      s hs0 hs1 hg).mpr hz

theorem hpRiemannHypothesis_iff_xi_critical_line :
    RiemannHypothesis ↔
      (∀ s : ℂ, hpRiemannXi s = 0 → s.re = 1 / 2) := by
  constructor
  · intro hRH s hxi
    obtain ⟨hz, hpos, _⟩ :=
      (hpRiemannXi_eq_zero_iff_zeta_and_critical_strip s).mp hxi
    have hs1 : s ≠ 1 :=
      (hpRiemannXi_zero_excludes_endpoints s hxi).2
    have hnt : ¬ ∃ n : ℕ, s = -2 * ((n : ℂ) + 1) := by
      rintro ⟨n, hn⟩
      have hre := congrArg Complex.re hn
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      norm_num [Complex.mul_re] at hre
      linarith
    exact hRH s hz hnt hs1
  · intro hline
    change
      ∀ s : ℂ, riemannZeta s = 0 →
        (¬ ∃ n : ℕ, s = -2 * ((n : ℂ) + 1)) →
        s ≠ 1 → s.re = 1 / 2
    intro s hz hnt hs1
    exact hline s
      (hpRiemannXi_eq_zero_of_nontrivial_zeta_zero s hz hnt hs1)

theorem hpRiemannHypothesis_iff_critical_real_zeros :
    RiemannHypothesis ↔
      (∀ t : ℂ, hpRiemannXiCritical t = 0 → t.im = 0) := by
  exact hpRiemannHypothesis_iff_xi_critical_line.trans
    hpRiemannXi_critical_line_iff_critical_real_zeros

theorem hpRiemannHypothesis_iff_zeta_strip_critical_line :
    RiemannHypothesis ↔
      (∀ s : ℂ, riemannZeta s = 0 →
        0 < s.re → s.re < 1 → s.re = 1 / 2) := by
  exact hpRiemannHypothesis_iff_xi_critical_line.trans
    hpRiemannXi_critical_line_iff_zeta_strip_critical_line

end HodgeProofHP

#print axioms HodgeProofHP.hpRiemannZeta_zero_ne_zero
#print axioms HodgeProofHP.hpRiemannZeta_nontrivial_zero_gamma_ne_zero
#print axioms HodgeProofHP.hpRiemannXi_eq_zero_of_nontrivial_zeta_zero
#print axioms HodgeProofHP.hpRiemannHypothesis_iff_xi_critical_line
#print axioms HodgeProofHP.hpRiemannHypothesis_iff_critical_real_zeros
#print axioms HodgeProofHP.hpRiemannHypothesis_iff_zeta_strip_critical_line
LEAN

lake build HodgeProofHP.Stage4RiemannXiRealZeroCriterion
lake env lean HodgeProofHP/Stage4RiemannHypothesisEquivalence.lean
lake build HodgeProofHP.Stage4RiemannHypothesisEquivalence
