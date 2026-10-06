#!/usr/bin/env bash
set -euo pipefail

lake build HodgeProofHP.Stage4ThetaHankelSpectralTraceApiAudit

target="HodgeProofHP/Stage4ThetaHankelSpectralSummability.lean"

if [ -f "$target" ]; then
  cp -p "$target" "$target.before_update_$(date +%Y%m%d_%H%M%S)"
fi

cat > "$target" <<'LEAN'
import HodgeProofHP.Stage4ThetaHankelSpectralTraceApiAudit
import HodgeProofHP.Stage4ThetaHankelSeparability
import Mathlib.Topology.Bases

/-!
Countability of the spectral basis index and summability of
the eigenvalues of the theta Hankel adjoint square.
Eigenvalues are indexed by basis vectors, including multiplicities.
-/

namespace HodgeProofHP

theorem hpThetaHankelSpectralBasis_dist_sq
    (i j : HPThetaHankelSpectralIndex) (hij : i ≠ j) :
    dist (hpThetaHankelSpectralBasis i)
      (hpThetaHankelSpectralBasis j) ^ 2 = 2 := by
  have hinner :
      inner ℂ (hpThetaHankelSpectralBasis i)
        (hpThetaHankelSpectralBasis j) = 0 :=
    hpThetaHankelSpectralBasis_orthonormal.inner_eq_zero hij
  rw [dist_eq_norm, norm_sub_sq (𝕜 := ℂ)]
  norm_num [hpThetaHankelSpectralBasis_norm, hinner]

theorem hpThetaHankelSpectralBasis_balls_disjoint :
    Pairwise (fun i j : HPThetaHankelSpectralIndex =>
      Disjoint
        (Metric.ball (hpThetaHankelSpectralBasis i) (1 / 2 : ℝ))
        (Metric.ball (hpThetaHankelSpectralBasis j) (1 / 2 : ℝ))) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  have hi :
      dist x (hpThetaHankelSpectralBasis i) < (1 / 2 : ℝ) :=
    Metric.mem_ball.mp hxi
  have hj :
      dist x (hpThetaHankelSpectralBasis j) < (1 / 2 : ℝ) :=
    Metric.mem_ball.mp hxj
  have htriangle :=
    dist_triangle (hpThetaHankelSpectralBasis i) x
      (hpThetaHankelSpectralBasis j)
  rw [dist_comm (hpThetaHankelSpectralBasis i) x] at htriangle
  have hlt :
      dist (hpThetaHankelSpectralBasis i)
        (hpThetaHankelSpectralBasis j) < 1 := by
    linarith
  have hnonneg :
      0 ≤ dist (hpThetaHankelSpectralBasis i)
        (hpThetaHankelSpectralBasis j) :=
    dist_nonneg
  have hsq := hpThetaHankelSpectralBasis_dist_sq i j hij
  nlinarith

theorem hpThetaHankelSpectralIndex_countable :
    Countable HPThetaHankelSpectralIndex := by
  exact
    hpThetaHankelSpectralBasis_balls_disjoint.countable_of_isOpen_disjoint
      (fun _ => Metric.isOpen_ball)
      (fun i => ⟨hpThetaHankelSpectralBasis i,
        Metric.mem_ball_self (by norm_num)⟩)

instance hpThetaHankelSpectralIndex_countableInstance :
    Countable HPThetaHankelSpectralIndex :=
  hpThetaHankelSpectralIndex_countable

theorem hpThetaHankelSpectralValues_re_hasSum :
    HasSum (fun i : HPThetaHankelSpectralIndex => i.1.re)
      hpThetaFirstTraceEnergy := by
  have hfun :
      (fun i : HPThetaHankelSpectralIndex => i.1.re) =
      (fun i : HPThetaHankelSpectralIndex =>
        ‖hpThetaHankelOperator (hpThetaHankelSpectralBasis i)‖ ^ 2) := by
    funext i
    exact hpThetaHankelSpectralValue_re_eq_energy i
  rw [hfun]
  exact hpThetaHankelBasis_norm_sq_hasSum_energy
    hpThetaHankelSpectralBasis

theorem hpThetaHankelSpectralValues_re_summable :
    Summable (fun i : HPThetaHankelSpectralIndex => i.1.re) :=
  hpThetaHankelSpectralValues_re_hasSum.summable

theorem hpThetaHankelSpectralValues_re_tsum :
    (∑' i : HPThetaHankelSpectralIndex, i.1.re) =
      hpThetaFirstTraceEnergy :=
  hpThetaHankelSpectralValues_re_hasSum.tsum_eq

#print axioms hpThetaHankelSpectralBasis_dist_sq
#print axioms hpThetaHankelSpectralIndex_countable
#print axioms hpThetaHankelSpectralValues_re_hasSum
#print axioms hpThetaHankelSpectralValues_re_summable
#print axioms hpThetaHankelSpectralValues_re_tsum

end HodgeProofHP
LEAN

lake env lean "$target"
lake build HodgeProofHP.Stage4ThetaHankelSpectralSummability

printf '%s\n' 'PASS: Stage4ThetaHankelSpectralSummability'
