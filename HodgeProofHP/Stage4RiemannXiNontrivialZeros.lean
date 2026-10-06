import HodgeProofHP.Stage4RiemannHypothesisEquivalence
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Nontrivial zeta zeros and the critical xi zero strip

These results identify zero sets and bound the imaginary coordinate.
They do not establish reality of all critical xi zeros.
-/

noncomputable section

namespace HodgeProofHP

theorem hpRiemannXi_zero_not_trivial
    (s : ℂ) (hxi : hpRiemannXi s = 0) :
    ¬ ∃ n : ℕ, s = -2 * ((n : ℂ) + 1) := by
  have hpos : 0 < s.re :=
    (hpRiemannXi_zero_mem_critical_strip s hxi).1
  rintro ⟨n, hn⟩
  have hre := congrArg Complex.re hn
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  norm_num [Complex.mul_re] at hre
  linarith

theorem hpRiemannXi_eq_zero_iff_nontrivial_zeta_zero
    (s : ℂ) :
    hpRiemannXi s = 0 ↔
      riemannZeta s = 0 ∧
      (¬ ∃ n : ℕ, s = -2 * ((n : ℂ) + 1)) ∧
      s ≠ 1 := by
  constructor
  · intro hxi
    have hz : riemannZeta s = 0 :=
      ((hpRiemannXi_eq_zero_iff_zeta_and_critical_strip s).mp hxi).1
    exact ⟨hz, hpRiemannXi_zero_not_trivial s hxi,
      (hpRiemannXi_zero_excludes_endpoints s hxi).2⟩
  · rintro ⟨hz, hnt, hs1⟩
    exact hpRiemannXi_eq_zero_of_nontrivial_zeta_zero s hz hnt hs1

theorem hpRiemannZeta_nontrivial_zero_mem_critical_strip
    (s : ℂ)
    (hz : riemannZeta s = 0)
    (hnt : ¬ ∃ n : ℕ, s = -2 * ((n : ℂ) + 1))
    (hs1 : s ≠ 1) :
    0 < s.re ∧ s.re < 1 := by
  exact hpRiemannXi_zero_mem_critical_strip s
    (hpRiemannXi_eq_zero_of_nontrivial_zeta_zero s hz hnt hs1)

theorem hpRiemannXiCritical_zero_im_bounds
    (t : ℂ) (ht : hpRiemannXiCritical t = 0) :
    -(1 / 2 : ℝ) < t.im ∧ t.im < (1 / 2 : ℝ) := by
  have hxi :
      hpRiemannXi ((1 / 2 : ℂ) + Complex.I * t) = 0 := by
    change hpRiemannXi ((1 / 2 : ℂ) + Complex.I * t) = 0 at ht
    exact ht
  obtain ⟨hlo, hhi⟩ :=
    hpRiemannXi_zero_mem_critical_strip
      ((1 / 2 : ℂ) + Complex.I * t) hxi
  rw [hpRiemannXiCritical_argument_re t] at hlo hhi
  constructor
  · linarith
  · linarith

end HodgeProofHP

#print axioms HodgeProofHP.hpRiemannXi_zero_not_trivial
#print axioms HodgeProofHP.hpRiemannXi_eq_zero_iff_nontrivial_zeta_zero
#print axioms HodgeProofHP.hpRiemannZeta_nontrivial_zero_mem_critical_strip
#print axioms HodgeProofHP.hpRiemannXiCritical_zero_im_bounds
