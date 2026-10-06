#!/usr/bin/env bash
set -euo pipefail

cat > HodgeProofHP/Stage3GaussianGroundApi.lean <<'LEAN'
import HodgeProofHP.Stage3ClosureDomainSpec
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.RingTheory.Polynomial.Hermite.Gaussian

/-!
The Gaussian ground-state function and its first integrability fact.
This file makes no eigenvector or spectral claim.
-/

namespace HodgeProofHP

private def hpGaussianGroundFunction (x : ℝ) : ℂ :=
  Complex.exp (-(1 / 2 : ℂ) * (x : ℂ) ^ 2)

private theorem hpGaussianGroundFunction_integrable :
    MeasureTheory.Integrable hpGaussianGroundFunction MeasureTheory.volume := by
  exact integrable_cexp_neg_mul_sq (b := (1 / 2 : ℂ)) (by norm_num)

#check Polynomial.deriv_gaussian_eq_hermite_mul_gaussian
#check MeasureTheory.MemLp
#check SchwartzMap.toLp

end HodgeProofHP
LEAN

lake env lean HodgeProofHP/Stage3GaussianGroundApi.lean
lake build HodgeProofHP.Stage3GaussianGroundApi
