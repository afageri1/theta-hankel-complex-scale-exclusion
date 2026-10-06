#!/usr/bin/env bash
set -euo pipefail

cat > HodgeProofHP/Stage3FormalSymmetry.lean <<'LEAN'
import HodgeProofHP.Stage3HarmonicInnerSymmetry
import HodgeProofHP.Stage3HarmonicCoreOperator

/-!
The harmonic oscillator core operator is formally symmetric on its Schwartz domain.
-/

namespace HodgeProofHP

theorem hpHarmonicCoreOperator_isFormalAdjoint :
    HPHarmonicCoreOperator.IsFormalAdjoint
      HPHarmonicCoreOperator := by
  intro u v
  obtain ⟨f, rfl⟩ := hpSchwartzCoreEquiv.surjective u
  obtain ⟨g, rfl⟩ := hpSchwartzCoreEquiv.surjective v
  change
    inner ℂ
      (HPHarmonicCoreOperator.toFun (hpSchwartzCoreEquiv f))
      (hpSchwartzCoreEquiv g : HPSpace) =
    inner ℂ
      (hpSchwartzCoreEquiv f : HPSpace)
      (HPHarmonicCoreOperator.toFun (hpSchwartzCoreEquiv g))
  rw [hpHarmonicCoreOperator_apply f,
    hpHarmonicCoreOperator_apply g]
  change
    inner ℂ (hpSchwartzHarmonicToL2 f) (hpSchwartzToL2 g) =
      inner ℂ (hpSchwartzToL2 f) (hpSchwartzHarmonicToL2 g)
  exact (hpSchwartz_harmonic_inner_symmetry f g).symm

#print axioms hpHarmonicCoreOperator_isFormalAdjoint

end HodgeProofHP
LEAN

lake build HodgeProofHP.Stage3FormalSymmetry
