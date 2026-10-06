#!/usr/bin/env bash
set -euo pipefail

lake build HodgeProofHP.Stage4ThetaHankelBasisTotalEnergy

target="HodgeProofHP/Stage4ThetaHankelDiagonalEnergy.lean"

if [ -f "$target" ]; then
  cp -p "$target" "$target.before_update_$(date +%Y%m%d_%H%M%S)"
fi

cat > "$target" <<'LEAN'
import HodgeProofHP.Stage4ThetaHankelBasisTotalEnergy
import HodgeProofHP.Stage4ThetaHankelAdjointSquarePairing
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
Real summability of basis norm energy and the diagonal identity for A* A.
These results do not define a Fredholm determinant.
-/

namespace HodgeProofHP

open MeasureTheory

theorem hpThetaHankelBasis_norm_sq_summable
    {ι : Type*} [Countable ι]
    (b : HilbertBasis ι ℂ HPThetaHankelSpace) :
    Summable (fun i => ‖hpThetaHankelOperator (b i)‖ ^ 2) := by
  have hs :=
    ENNReal.summable_toReal
      (ne_of_lt (hpThetaHankelBasis_norm_sq_tsum_lt_top b))
  have hpoint :
      (fun i =>
        (ENNReal.ofReal
          (‖hpThetaHankelOperator (b i)‖ ^ 2)).toReal) =
      (fun i => ‖hpThetaHankelOperator (b i)‖ ^ 2) := by
    funext i
    exact ENNReal.toReal_ofReal (sq_nonneg _)
  rw [hpoint] at hs
  exact hs

theorem hpThetaHankelBasis_norm_sq_tsum_real_eq_energy
    {ι : Type*} [Countable ι]
    (b : HilbertBasis ι ℂ HPThetaHankelSpace) :
    (∑' i, ‖hpThetaHankelOperator (b i)‖ ^ 2) =
      hpThetaFirstTraceEnergy := by
  have hs := hpThetaHankelBasis_norm_sq_summable b
  have h := hpThetaHankelBasis_norm_sq_tsum_eq_firstTraceEnergy b
  have hnonneg :
      ∀ i, 0 ≤ ‖hpThetaHankelOperator (b i)‖ ^ 2 :=
    fun i => sq_nonneg _
  have hE : 0 ≤ hpThetaFirstTraceEnergy := by
    rw [← hpThetaHankelRowEnergy_integral_eq_firstTraceEnergy]
    exact integral_nonneg (fun x => hpThetaHankelRowEnergy_nonneg x)
  have hcast :
      ENNReal.ofReal
        (∑' i, ‖hpThetaHankelOperator (b i)‖ ^ 2) =
      ENNReal.ofReal hpThetaFirstTraceEnergy :=
    (ENNReal.ofReal_tsum_of_nonneg hnonneg hs).trans h
  have hreal := congrArg ENNReal.toReal hcast
  rw [ENNReal.toReal_ofReal (tsum_nonneg hnonneg),
    ENNReal.toReal_ofReal hE] at hreal
  exact hreal

theorem hpThetaHankelBasis_norm_sq_hasSum_energy
    {ι : Type*} [Countable ι]
    (b : HilbertBasis ι ℂ HPThetaHankelSpace) :
    HasSum (fun i => ‖hpThetaHankelOperator (b i)‖ ^ 2)
      hpThetaFirstTraceEnergy := by
  have hs := (hpThetaHankelBasis_norm_sq_summable b).hasSum
  rw [hpThetaHankelBasis_norm_sq_tsum_real_eq_energy b] at hs
  exact hs

theorem hpThetaHankelAdjointSquare_diagonal_hasSum_energy
    {ι : Type*} [Countable ι]
    (b : HilbertBasis ι ℂ HPThetaHankelSpace) :
    HasSum
      (fun i =>
        (inner ℂ (b i) (hpThetaHankelAdjointSquare (b i))).re)
      hpThetaFirstTraceEnergy := by
  have hdiag :
      (fun i =>
        (inner ℂ (b i) (hpThetaHankelAdjointSquare (b i))).re) =
      (fun i => ‖hpThetaHankelOperator (b i)‖ ^ 2) := by
    funext i
    exact hpThetaHankelAdjointSquare_inner_re (b i)
  rw [hdiag]
  exact hpThetaHankelBasis_norm_sq_hasSum_energy b

theorem hpThetaHankelAdjointSquare_diagonal_summable
    {ι : Type*} [Countable ι]
    (b : HilbertBasis ι ℂ HPThetaHankelSpace) :
    Summable
      (fun i =>
        (inner ℂ (b i) (hpThetaHankelAdjointSquare (b i))).re) :=
  (hpThetaHankelAdjointSquare_diagonal_hasSum_energy b).summable

theorem hpThetaHankelAdjointSquare_diagonal_tsum_eq_energy
    {ι : Type*} [Countable ι]
    (b : HilbertBasis ι ℂ HPThetaHankelSpace) :
    (∑' i,
      (inner ℂ (b i) (hpThetaHankelAdjointSquare (b i))).re) =
      hpThetaFirstTraceEnergy :=
  (hpThetaHankelAdjointSquare_diagonal_hasSum_energy b).tsum_eq

#print axioms hpThetaHankelBasis_norm_sq_summable
#print axioms hpThetaHankelBasis_norm_sq_tsum_real_eq_energy
#print axioms hpThetaHankelBasis_norm_sq_hasSum_energy
#print axioms hpThetaHankelAdjointSquare_diagonal_hasSum_energy
#print axioms hpThetaHankelAdjointSquare_diagonal_summable
#print axioms hpThetaHankelAdjointSquare_diagonal_tsum_eq_energy

end HodgeProofHP
LEAN

lake env lean "$target"
lake build HodgeProofHP.Stage4ThetaHankelDiagonalEnergy

printf '%s\n' 'PASS: Stage4ThetaHankelDiagonalEnergy'
