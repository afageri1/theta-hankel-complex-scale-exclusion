#!/usr/bin/env bash
set -euo pipefail

lake build HodgeProofHP.Stage4ThetaHankelDiagonalEnergy

target="HodgeProofHP/Stage4ThetaHankelDiagonalObstruction.lean"

if [ -f "$target" ]; then
  cp -p "$target" "$target.before_update_$(date +%Y%m%d_%H%M%S)"
fi

cat > "$target" <<'LEAN'
import HodgeProofHP.Stage4ThetaHankelDiagonalEnergy
import HodgeProofHP.Stage4ThetaFirstTraceObstruction

/-!
Basis independence and the first-coefficient obstruction
for the real diagonal sum of the theta Hankel adjoint square.

No Fredholm determinant identity is assumed or defined.
-/

namespace HodgeProofHP

theorem hpThetaHankelAdjointSquare_diagonal_basis_independent
    {ι κ : Type*} [Countable ι] [Countable κ]
    (b : HilbertBasis ι ℂ HPThetaHankelSpace)
    (c : HilbertBasis κ ℂ HPThetaHankelSpace) :
    (∑' i,
      (inner ℂ (b i) (hpThetaHankelAdjointSquare (b i))).re) =
    ∑' j,
      (inner ℂ (c j) (hpThetaHankelAdjointSquare (c j))).re := by
  rw [hpThetaHankelAdjointSquare_diagonal_tsum_eq_energy b,
    hpThetaHankelAdjointSquare_diagonal_tsum_eq_energy c]

theorem hpThetaHankelAdjointSquare_diagonal_gt_momentRatio
    {ι : Type*} [Countable ι]
    (b : HilbertBasis ι ℂ HPThetaHankelSpace) :
    hpThetaXiMomentRatio <
      ∑' i,
        (inner ℂ (b i) (hpThetaHankelAdjointSquare (b i))).re := by
  rw [hpThetaHankelAdjointSquare_diagonal_tsum_eq_energy b]
  exact hpThetaFirstTraceEnergy_gt_momentRatio

theorem hpThetaHankelAdjointSquare_diagonal_ne_momentRatio
    {ι : Type*} [Countable ι]
    (b : HilbertBasis ι ℂ HPThetaHankelSpace) :
    (∑' i,
      (inner ℂ (b i) (hpThetaHankelAdjointSquare (b i))).re) ≠
      hpThetaXiMomentRatio := by
  rw [hpThetaHankelAdjointSquare_diagonal_tsum_eq_energy b]
  exact hpThetaFirstTraceEnergy_ne_momentRatio

theorem hpThetaHankelAdjointSquare_diagonal_ne_xiRatio
    {ι : Type*} [Countable ι]
    (b : HilbertBasis ι ℂ HPThetaHankelSpace) :
    (∑' i,
      (inner ℂ (b i) (hpThetaHankelAdjointSquare (b i))).re) ≠
      -(deriv (deriv hpRiemannXiCritical) 0).re /
        (2 * (hpRiemannXiCritical 0).re) := by
  rw [hpThetaHankelAdjointSquare_diagonal_tsum_eq_energy b]
  exact hpThetaFirstTraceEnergy_ne_xi_secondDeriv_ratio

theorem hpThetaHankelAdjointSquare_diagonal_not_hasSum_momentRatio
    {ι : Type*} [Countable ι]
    (b : HilbertBasis ι ℂ HPThetaHankelSpace) :
    ¬ HasSum
      (fun i =>
        (inner ℂ (b i) (hpThetaHankelAdjointSquare (b i))).re)
      hpThetaXiMomentRatio := by
  intro h
  exact
    hpThetaHankelAdjointSquare_diagonal_ne_momentRatio b
      h.tsum_eq

#print axioms hpThetaHankelAdjointSquare_diagonal_basis_independent
#print axioms hpThetaHankelAdjointSquare_diagonal_gt_momentRatio
#print axioms hpThetaHankelAdjointSquare_diagonal_ne_momentRatio
#print axioms hpThetaHankelAdjointSquare_diagonal_ne_xiRatio
#print axioms hpThetaHankelAdjointSquare_diagonal_not_hasSum_momentRatio

end HodgeProofHP
LEAN

lake env lean "$target"
lake build HodgeProofHP.Stage4ThetaHankelDiagonalObstruction

printf '%s\n' 'PASS: Stage4ThetaHankelDiagonalObstruction'
