#!/usr/bin/env bash
set -euo pipefail

mkdir -p HodgeProofHP

cat > HodgeProofHP/Stage4DirectHarmonicBridgeObstruction.lean <<'LEAN'
import HodgeProofHP.Stage4SpectralBridgeApiAudit
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Obstruction to a direct harmonic spectral bridge

The harmonic spectrum consists of positive odd integers.
The critical xi function is even.

Consequently, a hypothesis placing every critical xi zero directly
in this spectrum would imply that the critical xi function has no zeros.
No spectral correspondence is assumed as an established theorem.
-/

noncomputable section

namespace HodgeProofHP

theorem hpHarmonicSpectrum_neg_not_mem
    (t : ℂ) (ht : t ∈ hpHarmonicClosureSpectrum) :
    -t ∉ hpHarmonicClosureSpectrum := by
  intro hneg
  obtain ⟨n, hn⟩ :=
    (hpHarmonicClosure_mem_spectrum_iff t).mp ht
  obtain ⟨m, hm⟩ :=
    (hpHarmonicClosure_mem_spectrum_iff (-t)).mp hneg
  have hnre := congrArg Complex.re hn
  have hmre := congrArg Complex.re hm
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  norm_num [Complex.mul_re] at hnre hmre
  linarith

theorem hpDirectXiHarmonicBridge_implies_no_zeros
    (hbridge :
      ∀ t : ℂ, hpRiemannXiCritical t = 0 →
        t ∈ hpHarmonicClosureSpectrum)
    (t : ℂ) :
    hpRiemannXiCritical t ≠ 0 := by
  intro ht
  have hneg : hpRiemannXiCritical (-t) = 0 := by
    rw [hpRiemannXiCritical_even t]
    exact ht
  exact hpHarmonicSpectrum_neg_not_mem t (hbridge t ht)
    (hbridge (-t) hneg)

theorem hpDirectXiHarmonicBridge_obstructed_of_exists_zero
    (hzero : ∃ t : ℂ, hpRiemannXiCritical t = 0) :
    ¬ (∀ t : ℂ, hpRiemannXiCritical t = 0 →
      t ∈ hpHarmonicClosureSpectrum) := by
  intro hbridge
  obtain ⟨t, ht⟩ := hzero
  exact hpDirectXiHarmonicBridge_implies_no_zeros hbridge t ht

end HodgeProofHP

#print axioms HodgeProofHP.hpHarmonicSpectrum_neg_not_mem
#print axioms HodgeProofHP.hpDirectXiHarmonicBridge_implies_no_zeros
#print axioms HodgeProofHP.hpDirectXiHarmonicBridge_obstructed_of_exists_zero
LEAN

lake build HodgeProofHP.Stage4SpectralBridgeApiAudit
lake env lean HodgeProofHP/Stage4DirectHarmonicBridgeObstruction.lean
lake build HodgeProofHP.Stage4DirectHarmonicBridgeObstruction
