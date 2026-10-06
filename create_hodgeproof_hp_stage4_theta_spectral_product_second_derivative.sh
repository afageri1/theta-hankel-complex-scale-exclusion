#!/usr/bin/env bash
set -euo pipefail

lake build HodgeProofHP.Stage4ThetaHankelFiniteSpectralSecondDerivative

target="HodgeProofHP/Stage4ThetaHankelSpectralProductSecondDerivative.lean"

if [ -f "$target" ]; then
  cp -p "$target" "$target.before_update_$(date +%Y%m%d_%H%M%S)"
fi

cat > "$target" <<'LEAN'
import HodgeProofHP.Stage4ThetaHankelFiniteSpectralSecondDerivative

/-!
Pass the finite second-derivative identity to the spectral product.
The spectral sum and convergence of second derivatives are already proved.
No Xi correspondence is assumed.
-/

namespace HodgeProofHP

theorem hpThetaHankelFiniteSpectralProduct_secondDeriv_zero_tendsto_energy :
    Filter.Tendsto
      (fun F : Finset HPThetaHankelSpectralIndex =>
        deriv (deriv (hpThetaHankelFiniteSpectralProduct F)) 0)
      Filter.atTop
      (nhds ((-2 : ℂ) * (hpThetaFirstTraceEnergy : ℂ))) := by
  have hs :
      Filter.Tendsto
        (fun F : Finset HPThetaHankelSpectralIndex =>
          ∑ i ∈ F, i.1)
        Filter.atTop
        (nhds (hpThetaFirstTraceEnergy : ℂ)) :=
    hpThetaHankelSpectralValues_hasSum
  have hm :
      Filter.Tendsto
        (fun F : Finset HPThetaHankelSpectralIndex =>
          (-2 : ℂ) * (∑ i ∈ F, i.1))
        Filter.atTop
        (nhds ((-2 : ℂ) * (hpThetaFirstTraceEnergy : ℂ))) :=
    tendsto_const_nhds.mul hs
  simpa only [hpThetaHankelFiniteSpectralProduct_secondDeriv_zero] using hm

theorem hpThetaHankelSpectralProduct_secondDeriv_zero :
    deriv (deriv hpThetaHankelSpectralProduct) 0 =
      (-2 : ℂ) * (hpThetaFirstTraceEnergy : ℂ) := by
  exact tendsto_nhds_unique
    hpThetaHankelFiniteSpectralProduct_secondDeriv_zero_tendsto
    hpThetaHankelFiniteSpectralProduct_secondDeriv_zero_tendsto_energy

theorem hpThetaHankelSpectralProduct_secondCoefficient :
    deriv (deriv hpThetaHankelSpectralProduct) 0 / 2 =
      -(hpThetaFirstTraceEnergy : ℂ) := by
  rw [hpThetaHankelSpectralProduct_secondDeriv_zero]
  ring

theorem hpThetaHankelSpectralProduct_secondDeriv_zero_re :
    (deriv (deriv hpThetaHankelSpectralProduct) 0).re =
      -2 * hpThetaFirstTraceEnergy := by
  rw [hpThetaHankelSpectralProduct_secondDeriv_zero]
  simp

-- Inspect the exact interface before applying the Xi obstruction.
#check hpThetaHankel_function_ne_normalizedXi_of_trace_identity
#check hpThetaNormalizedXi_secondDeriv_zero
#check hpThetaNormalizedXi_secondCoefficient

#print axioms hpThetaHankelFiniteSpectralProduct_secondDeriv_zero_tendsto_energy
#print axioms hpThetaHankelSpectralProduct_secondDeriv_zero
#print axioms hpThetaHankelSpectralProduct_secondCoefficient
#print axioms hpThetaHankelSpectralProduct_secondDeriv_zero_re

end HodgeProofHP
LEAN

lake env lean "$target"
lake build HodgeProofHP.Stage4ThetaHankelSpectralProductSecondDerivative

printf '%s\n' 'PASS: Stage4ThetaHankelSpectralProductSecondDerivative'
