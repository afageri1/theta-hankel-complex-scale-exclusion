#!/usr/bin/env bash
set -euo pipefail

lake build HodgeProofHP.Stage4ThetaFourthDerivativeProductRule

target="HodgeProofHP/Stage4ThetaHankelFiniteSpectralFourthDerivative.lean"

if [ -f "$target" ]; then
  backup="$target.before_update_$(date +%Y%m%d_%H%M%S)"
  cp -p "$target" "$backup"
  printf 'BACKUP: %s\n' "$backup"
fi

cat > "$target" <<'LEAN'
import HodgeProofHP.Stage4ThetaFourthDerivativeProductRule

/-!
Fourth derivative at zero of the finite spectral product.
The formula is expressed through the first two finite spectral power sums.
-/

namespace HodgeProofHP

theorem hpThetaHankelSpectralProductFactor_secondDeriv_function
    (i : HPThetaHankelSpectralIndex) :
    deriv (deriv (hpThetaHankelSpectralProductFactor i)) =
      (fun _ : ℂ => -2 * i.1) := by
  rw [hpThetaHankelSpectralProductFactor_deriv]
  funext z
  have h := ((hasDerivAt_id z).const_mul (-2 * i.1)).deriv
  simp only [mul_one] at h
  convert h using 1 <;> rfl

theorem hpThetaHankelSpectralProductFactor_fourthDeriv_zero
    (i : HPThetaHankelSpectralIndex) :
    hpThetaIteratedComplexDeriv 4
      (hpThetaHankelSpectralProductFactor i) 0 = 0 := by
  change
    deriv (deriv
      (deriv (deriv (hpThetaHankelSpectralProductFactor i)))) 0 = 0
  rw [hpThetaHankelSpectralProductFactor_secondDeriv_function]
  simp

private theorem hpThetaHankelSpectralProductFactor_iteratedTwo_zero
    (i : HPThetaHankelSpectralIndex) :
    hpThetaIteratedComplexDeriv 2
      (hpThetaHankelSpectralProductFactor i) 0 = -2 * i.1 := by
  change
    deriv (deriv (hpThetaHankelSpectralProductFactor i)) 0 =
      -2 * i.1
  exact hpThetaHankelSpectralProductFactor_secondDeriv_zero i

private theorem hpThetaHankelFiniteSpectralProduct_iteratedTwo_zero
    (F : Finset HPThetaHankelSpectralIndex) :
    hpThetaIteratedComplexDeriv 2
      (hpThetaHankelFiniteSpectralProduct F) 0 =
        -2 * ∑ i ∈ F, i.1 := by
  change
    deriv (deriv (hpThetaHankelFiniteSpectralProduct F)) 0 =
      -2 * ∑ i ∈ F, i.1
  exact hpThetaHankelFiniteSpectralProduct_secondDeriv_zero F

theorem hpThetaHankelFiniteSpectralProduct_fourthDeriv_zero
    (F : Finset HPThetaHankelSpectralIndex) :
    hpThetaIteratedComplexDeriv 4
      (hpThetaHankelFiniteSpectralProduct F) 0 =
        12 * ((∑ i ∈ F, i.1) ^ 2 - ∑ i ∈ F, i.1 ^ 2) := by
  classical
  induction F using Finset.induction_on with
  | empty =>
      have hfun :
          hpThetaHankelFiniteSpectralProduct ∅ =
            (fun _ : ℂ => 1) := by
        funext z
        simp [hpThetaHankelFiniteSpectralProduct]
      rw [hfun]
      simp [hpThetaIteratedComplexDeriv]
  | @insert i F hi ih =>
      have hfun :
          hpThetaHankelFiniteSpectralProduct (insert i F) =
            (fun z =>
              hpThetaHankelSpectralProductFactor i z *
                hpThetaHankelFiniteSpectralProduct F z) := by
        funext z
        simp only [hpThetaHankelFiniteSpectralProduct,
          Finset.prod_insert hi]
      have hf0 :
          hpThetaHankelSpectralProductFactor i 0 = 1 := by
        simp [hpThetaHankelSpectralProductFactor]
      have hdf0 :
          deriv (hpThetaHankelSpectralProductFactor i) 0 = 0 := by
        rw [hpThetaHankelSpectralProductFactor_deriv]
        simp
      have hmul :=
        hpTheta_fourthDeriv_mul_normalized_zero
          (hpThetaHankelSpectralProductFactor i)
          (hpThetaHankelFiniteSpectralProduct F)
          (hpThetaHankelSpectralProductFactor_differentiable i)
          (hpThetaHankelFiniteSpectralProduct_differentiable F)
          hf0
          (hpThetaHankelFiniteSpectralProduct_zero F)
          hdf0
          (hpThetaHankelFiniteSpectralProduct_deriv_zero F)
      rw [hfun, hmul,
        hpThetaHankelSpectralProductFactor_iteratedTwo_zero,
        hpThetaHankelFiniteSpectralProduct_iteratedTwo_zero,
        hpThetaHankelSpectralProductFactor_fourthDeriv_zero,
        ih, Finset.sum_insert hi, Finset.sum_insert hi]
      ring

#print axioms hpThetaHankelSpectralProductFactor_secondDeriv_function
#print axioms hpThetaHankelSpectralProductFactor_fourthDeriv_zero
#print axioms hpThetaHankelFiniteSpectralProduct_fourthDeriv_zero

end HodgeProofHP
LEAN

lake env lean "$target"
lake build HodgeProofHP.Stage4ThetaHankelFiniteSpectralFourthDerivative

printf '%s\n' 'PASS: Stage4ThetaHankelFiniteSpectralFourthDerivative'
