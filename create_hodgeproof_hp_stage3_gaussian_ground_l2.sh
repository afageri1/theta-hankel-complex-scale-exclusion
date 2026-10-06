#!/usr/bin/env bash
set -euo pipefail

cat > HodgeProofHP/Stage3GaussianGroundL2.lean <<'LEAN'
import HodgeProofHP.Stage3GaussianGroundApi

/-!
The Gaussian ground state as an element of complex L².
-/

namespace HodgeProofHP

noncomputable def hpGaussianGroundL2 : HPSpace :=
  MeasureTheory.MemLp.toLp
    hpGaussianGroundFunction hpGaussianGroundFunction_memLp

theorem hpGaussianGroundL2_apply_ae :
    (hpGaussianGroundL2 : ℝ → ℂ) =ᵐ[MeasureTheory.volume]
      hpGaussianGroundFunction := by
  exact MeasureTheory.MemLp.coeFn_toLp hpGaussianGroundFunction_memLp

#check hpGaussianGroundL2
#print axioms hpGaussianGroundL2_apply_ae

end HodgeProofHP
LEAN

lake env lean HodgeProofHP/Stage3GaussianGroundL2.lean
lake build HodgeProofHP.Stage3GaussianGroundL2
