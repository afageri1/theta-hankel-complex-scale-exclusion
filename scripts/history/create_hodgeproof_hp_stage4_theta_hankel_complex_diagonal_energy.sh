#!/usr/bin/env bash
set -euo pipefail

lake build HodgeProofHP.Stage4ThetaHankelDiagonalObstruction

target="HodgeProofHP/Stage4ThetaHankelComplexDiagonalEnergy.lean"

if [ -f "$target" ]; then
  cp -p "$target" "$target.before_update_$(date +%Y%m%d_%H%M%S)"
fi

cat > "$target" <<'LEAN'
import HodgeProofHP.Stage4ThetaHankelDiagonalObstruction
import Mathlib.Analysis.Complex.Basic

/-!
Complex diagonal summability for the theta Hankel adjoint square.
The sum is computed from the operator, rather than defined to be E.
-/

namespace HodgeProofHP

theorem hpThetaHankelAdjointSquare_complex_diagonal_hasSum
    {ι : Type*} [Countable ι]
    (b : HilbertBasis ι ℂ HPThetaHankelSpace) :
    HasSum
      (fun i =>
        inner ℂ (b i) (hpThetaHankelAdjointSquare (b i)))
      (hpThetaFirstTraceEnergy : ℂ) := by
  have hcast :
      HasSum
        (fun i => ((‖hpThetaHankelOperator (b i)‖ ^ 2 : ℝ) : ℂ))
        (hpThetaFirstTraceEnergy : ℂ) := by
    simpa only [Function.comp_apply, Complex.ofRealCLM_apply] using
      (hpThetaHankelBasis_norm_sq_hasSum_energy b).mapL
        Complex.ofRealCLM
  have hdiag :
      (fun i =>
        inner ℂ (b i) (hpThetaHankelAdjointSquare (b i))) =
      (fun i => ((‖hpThetaHankelOperator (b i)‖ ^ 2 : ℝ) : ℂ)) := by
    funext i
    exact hpThetaHankelAdjointSquare_inner (b i)
  rw [hdiag]
  exact hcast

theorem hpThetaHankelAdjointSquare_complex_diagonal_summable
    {ι : Type*} [Countable ι]
    (b : HilbertBasis ι ℂ HPThetaHankelSpace) :
    Summable
      (fun i =>
        inner ℂ (b i) (hpThetaHankelAdjointSquare (b i))) :=
  (hpThetaHankelAdjointSquare_complex_diagonal_hasSum b).summable

theorem hpThetaHankelAdjointSquare_complex_diagonal_tsum_eq_energy
    {ι : Type*} [Countable ι]
    (b : HilbertBasis ι ℂ HPThetaHankelSpace) :
    (∑' i,
      inner ℂ (b i) (hpThetaHankelAdjointSquare (b i))) =
      (hpThetaFirstTraceEnergy : ℂ) :=
  (hpThetaHankelAdjointSquare_complex_diagonal_hasSum b).tsum_eq

theorem hpThetaHankelAdjointSquare_complex_diagonal_basis_independent
    {ι κ : Type*} [Countable ι] [Countable κ]
    (b : HilbertBasis ι ℂ HPThetaHankelSpace)
    (c : HilbertBasis κ ℂ HPThetaHankelSpace) :
    (∑' i,
      inner ℂ (b i) (hpThetaHankelAdjointSquare (b i))) =
    ∑' j,
      inner ℂ (c j) (hpThetaHankelAdjointSquare (c j)) := by
  rw [hpThetaHankelAdjointSquare_complex_diagonal_tsum_eq_energy b,
    hpThetaHankelAdjointSquare_complex_diagonal_tsum_eq_energy c]

theorem hpThetaHankelAdjointSquare_complex_diagonal_ne_momentRatio
    {ι : Type*} [Countable ι]
    (b : HilbertBasis ι ℂ HPThetaHankelSpace) :
    (∑' i,
      inner ℂ (b i) (hpThetaHankelAdjointSquare (b i))) ≠
      (hpThetaXiMomentRatio : ℂ) := by
  rw [hpThetaHankelAdjointSquare_complex_diagonal_tsum_eq_energy b]
  intro h
  have hr := congrArg Complex.re h
  simp only [Complex.ofReal_re] at hr
  exact hpThetaFirstTraceEnergy_ne_momentRatio hr

#print axioms hpThetaHankelAdjointSquare_complex_diagonal_hasSum
#print axioms hpThetaHankelAdjointSquare_complex_diagonal_summable
#print axioms hpThetaHankelAdjointSquare_complex_diagonal_tsum_eq_energy
#print axioms hpThetaHankelAdjointSquare_complex_diagonal_basis_independent
#print axioms hpThetaHankelAdjointSquare_complex_diagonal_ne_momentRatio

end HodgeProofHP
LEAN

lake env lean "$target"
lake build HodgeProofHP.Stage4ThetaHankelComplexDiagonalEnergy

printf '%s\n' 'PASS: Stage4ThetaHankelComplexDiagonalEnergy'
