#!/usr/bin/env bash
set -euo pipefail

mkdir -p HodgeProofHP

cat > HodgeProofHP/Stage4ThetaGaussianDerivatives.lean <<'LEAN'
import HodgeProofHP.Stage4RiemannXiCosineIntegral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Ring

/-!
First and second derivatives of individual logarithmic theta terms.
No interchange of differentiation and an infinite sum is used here.
-/

noncomputable section

namespace HodgeProofHP

/-- A Gaussian term in the logarithmic theta profile. -/
def hpThetaGaussianProfile (a u : ℝ) : ℝ :=
  2 * Real.exp (u / 2 - a * Real.exp (2 * u))

theorem hpThetaGaussianProfile_eq_product (a u : ℝ) :
    hpThetaGaussianProfile a u =
      2 * Real.exp (u / 2) *
        Real.exp (-a * Real.exp (2 * u)) := by
  unfold hpThetaGaussianProfile
  rw [show u / 2 - a * Real.exp (2 * u) =
    u / 2 + (-a * Real.exp (2 * u)) by ring,
    Real.exp_add]
  ring

theorem hpThetaGaussianProfile_hasDerivAt (a u : ℝ) :
    HasDerivAt (hpThetaGaussianProfile a)
      ((1 / 2 - 2 * a * Real.exp (2 * u)) *
        hpThetaGaussianProfile a u) u := by
  have hu := hasDerivAt_id u
  have he := (hu.const_mul 2).exp
  have hh := (hu.div_const 2).sub (he.const_mul a)
  change HasDerivAt
    (fun v : ℝ => v / 2 - a * Real.exp (2 * v))
    (1 / 2 - a * (Real.exp (2 * u) * (2 * 1))) u at hh
  have h := hh.exp.const_mul 2
  change HasDerivAt (hpThetaGaussianProfile a)
    (2 * (Real.exp (u / 2 - a * Real.exp (2 * u)) *
      (1 / 2 - a * (Real.exp (2 * u) * (2 * 1))))) u at h
  convert h using 1 <;>
    simp only [hpThetaGaussianProfile] <;> ring

theorem hpThetaGaussianProfile_deriv (a u : ℝ) :
    deriv (hpThetaGaussianProfile a) u =
      (1 / 2 - 2 * a * Real.exp (2 * u)) *
        hpThetaGaussianProfile a u :=
  (hpThetaGaussianProfile_hasDerivAt a u).deriv

theorem hpThetaGaussianProfile_deriv_function (a : ℝ) :
    deriv (hpThetaGaussianProfile a) =
      fun u => (1 / 2 - 2 * a * Real.exp (2 * u)) *
        hpThetaGaussianProfile a u := by
  funext u
  exact hpThetaGaussianProfile_deriv a u

theorem hpThetaGaussianProfile_first_hasDerivAt (a u : ℝ) :
    HasDerivAt
      (fun v => (1 / 2 - 2 * a * Real.exp (2 * v)) *
        hpThetaGaussianProfile a v)
      (((1 / 2 - 2 * a * Real.exp (2 * u)) ^ 2 -
        4 * a * Real.exp (2 * u)) *
        hpThetaGaussianProfile a u) u := by
  have hu := hasDerivAt_id u
  have he := (hu.const_mul 2).exp
  have hc :=
    (hasDerivAt_const u (1 / 2 : ℝ)).sub
      (he.const_mul (2 * a))
  change HasDerivAt
    (fun v : ℝ => 1 / 2 - 2 * a * Real.exp (2 * v))
    (0 - (2 * a) * (Real.exp (2 * u) * (2 * 1))) u at hc
  convert hc.mul (hpThetaGaussianProfile_hasDerivAt a u)
    using 1 <;> ring

theorem hpThetaGaussianProfile_secondDeriv (a u : ℝ) :
    deriv (deriv (hpThetaGaussianProfile a)) u =
      ((1 / 2 - 2 * a * Real.exp (2 * u)) ^ 2 -
        4 * a * Real.exp (2 * u)) *
        hpThetaGaussianProfile a u := by
  rw [hpThetaGaussianProfile_deriv_function]
  exact (hpThetaGaussianProfile_first_hasDerivAt a u).deriv

/-- The individual term of the differentiated theta kernel. -/
def hpThetaGaussianKernelTerm (a u : ℝ) : ℝ :=
  (4 * a ^ 2 * (Real.exp (2 * u)) ^ 2 -
    6 * a * Real.exp (2 * u)) *
    hpThetaGaussianProfile a u

theorem hpThetaGaussianProfile_secondDeriv_sub_quarter
    (a u : ℝ) :
    deriv (deriv (hpThetaGaussianProfile a)) u -
        (1 / 4) * hpThetaGaussianProfile a u =
      hpThetaGaussianKernelTerm a u := by
  rw [hpThetaGaussianProfile_secondDeriv]
  unfold hpThetaGaussianKernelTerm
  ring

/-- The parameter corresponding to the nth positive theta summand. -/
def hpThetaGaussianParameter (n : ℕ) : ℝ :=
  Real.pi * ((n : ℝ) + 1) ^ 2

theorem hpThetaGaussianProfile_theta_term (n : ℕ) (u : ℝ) :
    hpThetaGaussianProfile (hpThetaGaussianParameter n) u =
      Real.exp (u / 2) *
        (2 * Real.exp
          (-Real.pi * ((n : ℝ) + 1) ^ 2 *
            Real.exp (2 * u))) := by
  rw [hpThetaGaussianProfile_eq_product]
  unfold hpThetaGaussianParameter
  have hex :
      -(Real.pi * ((n : ℝ) + 1) ^ 2) * Real.exp (2 * u) =
        -Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp (2 * u) := by
    ring
  rw [hex]
  ring

#print axioms hpThetaGaussianProfile_eq_product
#print axioms hpThetaGaussianProfile_hasDerivAt
#print axioms hpThetaGaussianProfile_deriv
#print axioms hpThetaGaussianProfile_first_hasDerivAt
#print axioms hpThetaGaussianProfile_secondDeriv
#print axioms hpThetaGaussianProfile_secondDeriv_sub_quarter
#print axioms hpThetaGaussianProfile_theta_term

end HodgeProofHP
LEAN

lake build HodgeProofHP.Stage4RiemannXiCosineIntegral
lake env lean HodgeProofHP/Stage4ThetaGaussianDerivatives.lean
lake build HodgeProofHP.Stage4ThetaGaussianDerivatives
