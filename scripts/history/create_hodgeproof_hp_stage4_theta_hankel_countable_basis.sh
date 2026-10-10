#!/usr/bin/env bash
set -euo pipefail

lake build HodgeProofHP.Stage4ThetaHankelSeparability

target="HodgeProofHP/Stage4ThetaHankelCountableBasis.lean"

if [ -f "$target" ]; then
  cp -p "$target" "$target.before_update_$(date +%Y%m%d_%H%M%S)"
fi

cat > "$target" <<'LEAN'
import HodgeProofHP.Stage4ThetaHankelSeparability
import Mathlib.Topology.Bases
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
Countability of the chosen Hilbert basis, using disjoint open balls.
Then specialize the established diagonal-energy identity to this basis.
-/

namespace HodgeProofHP

theorem hpThetaHankelHilbertBasis_dist_sq
    (i j : hpThetaHankelBasisSet) (hij : i ≠ j) :
    dist (hpThetaHankelHilbertBasis i)
      (hpThetaHankelHilbertBasis j) ^ 2 = 2 := by
  have hon := hpThetaHankelHilbertBasis_orthonormal
  rw [dist_eq_norm, norm_sub_sq (𝕜 := ℂ)]
  rw [hon.norm_eq_one i, hon.norm_eq_one j,
    hon.inner_eq_zero hij]
  norm_num

theorem hpThetaHankelHilbertBasis_one_le_dist
    (i j : hpThetaHankelBasisSet) (hij : i ≠ j) :
    1 ≤ dist (hpThetaHankelHilbertBasis i)
      (hpThetaHankelHilbertBasis j) := by
  have hsq := hpThetaHankelHilbertBasis_dist_sq i j hij
  have hnonneg :
      0 ≤ dist (hpThetaHankelHilbertBasis i)
        (hpThetaHankelHilbertBasis j) :=
    dist_nonneg
  nlinarith

theorem hpThetaHankelHilbertBasis_balls_disjoint :
    Pairwise (fun i j : hpThetaHankelBasisSet =>
      Disjoint
        (Metric.ball (hpThetaHankelHilbertBasis i) (1 / 2 : ℝ))
        (Metric.ball (hpThetaHankelHilbertBasis j) (1 / 2 : ℝ))) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  have hi :
      dist x (hpThetaHankelHilbertBasis i) < (1 / 2 : ℝ) :=
    Metric.mem_ball.mp hxi
  have hj :
      dist x (hpThetaHankelHilbertBasis j) < (1 / 2 : ℝ) :=
    Metric.mem_ball.mp hxj
  have htriangle :=
    dist_triangle (hpThetaHankelHilbertBasis i) x
      (hpThetaHankelHilbertBasis j)
  have hsep := hpThetaHankelHilbertBasis_one_le_dist i j hij
  rw [dist_comm (hpThetaHankelHilbertBasis i) x] at htriangle
  linarith

theorem hpThetaHankelBasisSet_countable :
    Countable hpThetaHankelBasisSet := by
  exact
    hpThetaHankelHilbertBasis_balls_disjoint.countable_of_isOpen_disjoint
      (fun _ => Metric.isOpen_ball)
      (fun i => ⟨hpThetaHankelHilbertBasis i,
        Metric.mem_ball_self (by norm_num)⟩)

instance hpThetaHankelBasisSet_countableInstance :
    Countable hpThetaHankelBasisSet :=
  hpThetaHankelBasisSet_countable

theorem hpThetaHankelChosenBasis_norm_sq_hasSum_energy :
    HasSum
      (fun i : hpThetaHankelBasisSet =>
        ‖hpThetaHankelOperator (hpThetaHankelHilbertBasis i)‖ ^ 2)
      hpThetaFirstTraceEnergy := by
  exact hpThetaHankelBasis_norm_sq_hasSum_energy
    hpThetaHankelHilbertBasis

#print axioms hpThetaHankelHilbertBasis_dist_sq
#print axioms hpThetaHankelBasisSet_countable
#print axioms hpThetaHankelChosenBasis_norm_sq_hasSum_energy

end HodgeProofHP
LEAN

lake env lean "$target"
lake build HodgeProofHP.Stage4ThetaHankelCountableBasis

printf '%s\n' 'PASS: Stage4ThetaHankelCountableBasis'
