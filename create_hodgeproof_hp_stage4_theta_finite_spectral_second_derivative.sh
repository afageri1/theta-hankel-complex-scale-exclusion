#!/usr/bin/env bash
set -euo pipefail

lake build HodgeProofHP.Stage4ThetaHankelSpectralProductSecondDerivativeLimits

target="HodgeProofHP/Stage4ThetaHankelFiniteSpectralSecondDerivative.lean"

if [ -f "$target" ]; then
  cp -p "$target" "$target.before_update_$(date +%Y%m%d_%H%M%S)"
fi

cat > "$target" <<'LEAN'
import HodgeProofHP.Stage4ThetaHankelSpectralProductSecondDerivativeLimits
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
Compute the second derivative at zero of finite spectral products.
This calculation does not assume any correspondence with Riemann Xi.
-/

namespace HodgeProofHP

theorem hpTheta_secondDeriv_mul_zero
    (f g : ℂ → ℂ)
    (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g)
    (hf' : Differentiable ℂ (deriv f))
    (hg' : Differentiable ℂ (deriv g))
    (hf0 : f 0 = 1) (hg0 : g 0 = 1)
    (hdf0 : deriv f 0 = 0) (hdg0 : deriv g 0 = 0) :
    deriv (deriv (fun z => f z * g z)) 0 =
      deriv (deriv f) 0 + deriv (deriv g) 0 := by
  have hfun :
      deriv (fun z => f z * g z) =
        (fun z => deriv f z * g z + f z * deriv g z) := by
    funext z
    exact ((hf z).hasDerivAt.fun_mul (hg z).hasDerivAt).deriv
  have hleft :=
    (hf' 0).hasDerivAt.fun_mul (hg 0).hasDerivAt
  have hright :=
    (hf 0).hasDerivAt.fun_mul (hg' 0).hasDerivAt
  have hsum := hleft.add hright
  rw [hfun]
  have hd := hsum.deriv
  simp only [hf0, hg0, hdf0, hdg0, mul_one, one_mul,
    zero_mul, mul_zero, add_zero, zero_add] at hd
  convert hd using 1 <;> rfl

theorem hpThetaHankelSpectralProductFactor_hasDerivAt
    (i : HPThetaHankelSpectralIndex) (z : ℂ) :
    HasDerivAt (hpThetaHankelSpectralProductFactor i)
      ((-2 * i.1) * z) z := by
  have h :=
    (hasDerivAt_const z (1 : ℂ)).sub
      (((hasDerivAt_id z).pow 2).mul_const i.1)
  convert h using 1 <;>
    first
    | rfl
    | (funext w; rfl)
    | (norm_num [Pi.pow_apply] <;> ring)

theorem hpThetaHankelSpectralProductFactor_deriv
    (i : HPThetaHankelSpectralIndex) :
    deriv (hpThetaHankelSpectralProductFactor i) =
      (fun z : ℂ => (-2 * i.1) * z) := by
  funext z
  exact (hpThetaHankelSpectralProductFactor_hasDerivAt i z).deriv

theorem hpThetaHankelSpectralProductFactor_secondDeriv_zero
    (i : HPThetaHankelSpectralIndex) :
    deriv (deriv (hpThetaHankelSpectralProductFactor i)) 0 =
      -2 * i.1 := by
  rw [hpThetaHankelSpectralProductFactor_deriv]
  have h := ((hasDerivAt_id (0 : ℂ)).const_mul (-2 * i.1)).deriv
  simp only [mul_one] at h
  convert h using 1 <;> rfl

theorem hpThetaHankelFiniteSpectralProduct_secondDeriv_zero
    (F : Finset HPThetaHankelSpectralIndex) :
    deriv (deriv (hpThetaHankelFiniteSpectralProduct F)) 0 =
      -2 * ∑ i ∈ F, i.1 := by
  classical
  induction F using Finset.induction_on with
  | empty =>
      have hfun :
          hpThetaHankelFiniteSpectralProduct
            (∅ : Finset HPThetaHankelSpectralIndex) =
              (fun _ : ℂ => 1) := by
        funext z
        simp only [hpThetaHankelFiniteSpectralProduct, Finset.prod_empty]
      rw [hfun]
      simp
  | @insert i F hi ih =>
      have hfun :
          hpThetaHankelFiniteSpectralProduct (insert i F) =
            (fun z =>
              hpThetaHankelSpectralProductFactor i z *
                hpThetaHankelFiniteSpectralProduct F z) := by
        funext z
        simp only [hpThetaHankelFiniteSpectralProduct,
          Finset.prod_insert hi]
      have hf0 : hpThetaHankelSpectralProductFactor i 0 = 1 := by
        simp [hpThetaHankelSpectralProductFactor]
      have hdf0 :
          deriv (hpThetaHankelSpectralProductFactor i) 0 = 0 := by
        rw [hpThetaHankelSpectralProductFactor_deriv]
        simp
      have hmul :=
        hpTheta_secondDeriv_mul_zero
          (hpThetaHankelSpectralProductFactor i)
          (hpThetaHankelFiniteSpectralProduct F)
          (hpThetaHankelSpectralProductFactor_differentiable i)
          (hpThetaHankelFiniteSpectralProduct_differentiable F)
          (hpThetaHankelSpectralProductFactor_differentiable i).deriv
          (hpThetaHankelFiniteSpectralProduct_deriv_differentiable F)
          hf0
          (hpThetaHankelFiniteSpectralProduct_zero F)
          hdf0
          (hpThetaHankelFiniteSpectralProduct_deriv_zero F)
      rw [hfun, hmul,
        hpThetaHankelSpectralProductFactor_secondDeriv_zero, ih,
        Finset.sum_insert hi]
      ring

#print axioms hpTheta_secondDeriv_mul_zero
#print axioms hpThetaHankelSpectralProductFactor_hasDerivAt
#print axioms hpThetaHankelSpectralProductFactor_deriv
#print axioms hpThetaHankelSpectralProductFactor_secondDeriv_zero
#print axioms hpThetaHankelFiniteSpectralProduct_secondDeriv_zero

end HodgeProofHP
LEAN

lake env lean "$target"
lake build HodgeProofHP.Stage4ThetaHankelFiniteSpectralSecondDerivative

printf '%s\n' 'PASS: Stage4ThetaHankelFiniteSpectralSecondDerivative'
