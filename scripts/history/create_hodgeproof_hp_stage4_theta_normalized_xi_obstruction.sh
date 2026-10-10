#!/usr/bin/env bash
set -euo pipefail

lake build HodgeProofHP.Stage4ThetaHankelSecondCoefficientObstruction

target="HodgeProofHP/Stage4ThetaNormalizedXiObstruction.lean"

if [ -f "$target" ]; then
  cp -p "$target" "$target.before_update_$(date +%Y%m%d_%H%M%S)"
fi

cat > "$target" <<'LEAN'
import HodgeProofHP.Stage4ThetaHankelSecondCoefficientObstruction
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
Normalized xi and a conditional function-level obstruction.

No Fredholm determinant is constructed here.
The trace derivative identity remains an explicit hypothesis.
-/

namespace HodgeProofHP

noncomputable def hpThetaNormalizedXi (z : ℂ) : ℂ :=
  hpRiemannXiCritical z / hpRiemannXiCritical 0

theorem hpThetaXi_zero_eq_cast_re :
    ((hpRiemannXiCritical 0).re : ℂ) =
      hpRiemannXiCritical 0 := by
  rw [← hpThetaPhiMomentZero_cast_eq_xi_zero]
  simp

theorem hpTheta_deriv_div_const
    (f : ℂ → ℂ) (c : ℂ) :
    deriv (fun z => f z / c) =
      fun z => deriv f z / c := by
  funext z
  exact deriv_div_const c

theorem hpTheta_secondDeriv_div_const
    (f : ℂ → ℂ) (c : ℂ) :
    deriv (deriv (fun z => f z / c)) =
      fun z => deriv (deriv f) z / c := by
  rw [hpTheta_deriv_div_const]
  exact hpTheta_deriv_div_const (deriv f) c

theorem hpThetaNormalizedXi_secondDeriv_zero :
    deriv (deriv hpThetaNormalizedXi) 0 =
      deriv (deriv hpRiemannXiCritical) 0 /
        hpRiemannXiCritical 0 := by
  unfold hpThetaNormalizedXi
  rw [hpTheta_secondDeriv_div_const]

theorem hpThetaNormalizedXi_secondCoefficient :
    -(deriv (deriv hpThetaNormalizedXi) 0).re / 2 =
      -(deriv (deriv hpRiemannXiCritical) 0).re /
        (2 * (hpRiemannXiCritical 0).re) := by
  rw [hpThetaNormalizedXi_secondDeriv_zero]
  rw [← hpThetaXi_zero_eq_cast_re]
  simp only [div_eq_mul_inv, ← Complex.ofReal_inv,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero]
  ring

theorem hpThetaHankel_function_ne_normalizedXi_of_trace_identity
    {ι : Type*} [Countable ι]
    (b : HilbertBasis ι ℂ HPThetaHankelSpace)
    (D : ℂ → ℂ)
    (hD :
      (deriv (deriv D) 0).re =
        -2 *
          (hpThetaHankelBasisTrace b
            hpThetaHankelAdjointSquare).re) :
    D ≠ hpThetaNormalizedXi := by
  intro heq
  apply
    hpThetaHankel_secondCoefficient_ne_xiRatio_of_trace_identity
      b D hD
  rw [heq]
  exact hpThetaNormalizedXi_secondCoefficient

#print axioms hpThetaXi_zero_eq_cast_re
#print axioms hpThetaNormalizedXi_secondDeriv_zero
#print axioms hpThetaNormalizedXi_secondCoefficient
#print axioms hpThetaHankel_function_ne_normalizedXi_of_trace_identity

end HodgeProofHP
LEAN

lake env lean "$target"
lake build HodgeProofHP.Stage4ThetaNormalizedXiObstruction

printf '%s\n' 'PASS: Stage4ThetaNormalizedXiObstruction'
