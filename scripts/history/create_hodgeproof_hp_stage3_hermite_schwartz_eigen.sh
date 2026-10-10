#!/usr/bin/env bash
set -euo pipefail

cat > HodgeProofHP/Stage3HermiteSchwartzEigen.lean <<'LEAN'
import HodgeProofHP.Stage3GaussianSchwartzEigen

/-!
Eigen-equations for the recursively defined Hermite family
on Schwartz space. Completeness is not asserted.
-/

namespace HodgeProofHP

theorem hpHermiteSchwartz_eigen (n : ℕ) :
    hpSchwartzHarmonicAction (hpHermiteSchwartz n) =
      (2 * (n : ℂ) + 1) • hpHermiteSchwartz n := by
  induction n with
  | zero =>
      simpa only [hpHermiteSchwartz_zero, Nat.cast_zero,
        mul_zero, zero_add, one_smul] using
        hpComplexGaussian_schwartz_eigen
  | succ n ih =>
      change
        hpSchwartzHarmonicAction
            (hpSchwartzCreation (hpHermiteSchwartz n)) =
          (2 * ((n + 1 : ℕ) : ℂ) + 1) •
            hpSchwartzCreation (hpHermiteSchwartz n)
      rw [hpSchwartzHarmonicAction_creation, ih, map_smul]
      rw [← add_smul]
      have hscalar :
          (2 * (n : ℂ) + 1) + 2 =
            2 * ((n + 1 : ℕ) : ℂ) + 1 := by
        push_cast
        ring
      rw [hscalar]

#print axioms hpHermiteSchwartz_eigen

end HodgeProofHP
LEAN

lake env lean HodgeProofHP/Stage3HermiteSchwartzEigen.lean
lake build HodgeProofHP.Stage3HermiteSchwartzEigen
