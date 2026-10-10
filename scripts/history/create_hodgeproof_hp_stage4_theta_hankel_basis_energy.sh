#!/usr/bin/env bash
set -euo pipefail

lake build HodgeProofHP.Stage4ThetaHankelActionTonelli

target="HodgeProofHP/Stage4ThetaHankelBasisEnergy.lean"

if [ -f "$target" ]; then
  cp -p "$target" "$target.before_update_$(date +%Y%m%d_%H%M%S)"
fi

cat > "$target" <<'LEAN'
import HodgeProofHP.Stage4ThetaHankelActionTonelli
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
Parseval and Tonelli identify the basis action energy with
the integral of the theta Hankel row energy.
No operator trace is defined in this module.
-/

namespace HodgeProofHP

open MeasureTheory

theorem hpThetaHankelAction_parseval_ofReal_tsum
    {ι : Type*}
    (b : HilbertBasis ι ℂ HPThetaHankelSpace)
    (x : ℝ)
    (hx : MemLp (fun y => hpThetaHankelKernel x y)
      2 hpThetaHankelMeasure) :
    (∑' i,
      ENNReal.ofReal
        (‖hpThetaHankelActionFunction (b i) x‖ ^ 2)) =
      ENNReal.ofReal (hpThetaHankelRowEnergy x) := by
  have hs := hpThetaHankelAction_parseval_hasSum b x hx
  calc
    (∑' i, ENNReal.ofReal
        (‖hpThetaHankelActionFunction (b i) x‖ ^ 2)) =
        ENNReal.ofReal
          (∑' i, ‖hpThetaHankelActionFunction (b i) x‖ ^ 2) :=
      (ENNReal.ofReal_tsum_of_nonneg
        (fun i => sq_nonneg
          ‖hpThetaHankelActionFunction (b i) x‖)
        hs.summable).symm
    _ = ENNReal.ofReal (hpThetaHankelRowEnergy x) :=
      congrArg ENNReal.ofReal hs.tsum_eq

theorem hpThetaHankelAction_parseval_ofReal_tsum_ae
    {ι : Type*}
    (b : HilbertBasis ι ℂ HPThetaHankelSpace) :
    (fun x =>
      ∑' i, ENNReal.ofReal
        (‖hpThetaHankelActionFunction (b i) x‖ ^ 2))
      =ᵐ[hpThetaHankelMeasure]
    (fun x => ENNReal.ofReal (hpThetaHankelRowEnergy x)) := by
  filter_upwards [hpThetaHankelKernel_row_memLp_ae] with x hx
  exact hpThetaHankelAction_parseval_ofReal_tsum b x hx

theorem hpThetaHankelBasis_lintegral_tsum_eq_rowEnergy
    {ι : Type*}
    (b : HilbertBasis ι ℂ HPThetaHankelSpace) :
    (∫⁻ x,
      (∑' i, ENNReal.ofReal
        (‖hpThetaHankelActionFunction (b i) x‖ ^ 2))
      ∂hpThetaHankelMeasure) =
    ∫⁻ x, ENNReal.ofReal (hpThetaHankelRowEnergy x)
      ∂hpThetaHankelMeasure := by
  exact lintegral_congr_ae
    (hpThetaHankelAction_parseval_ofReal_tsum_ae b)

theorem hpThetaHankelBasis_tsum_lintegral_eq_rowEnergy
    {ι : Type*} [Countable ι]
    (b : HilbertBasis ι ℂ HPThetaHankelSpace) :
    (∑' i, ∫⁻ x,
      ENNReal.ofReal
        (‖hpThetaHankelActionFunction (b i) x‖ ^ 2)
      ∂hpThetaHankelMeasure) =
    ∫⁻ x, ENNReal.ofReal (hpThetaHankelRowEnergy x)
      ∂hpThetaHankelMeasure := by
  calc
    _ = ∫⁻ x,
        (∑' i, ENNReal.ofReal
          (‖hpThetaHankelActionFunction (b i) x‖ ^ 2))
        ∂hpThetaHankelMeasure :=
      hpThetaHankelBasis_sq_tsum_lintegral b
    _ = _ := hpThetaHankelBasis_lintegral_tsum_eq_rowEnergy b

#print axioms hpThetaHankelAction_parseval_ofReal_tsum
#print axioms hpThetaHankelAction_parseval_ofReal_tsum_ae
#print axioms hpThetaHankelBasis_lintegral_tsum_eq_rowEnergy
#print axioms hpThetaHankelBasis_tsum_lintegral_eq_rowEnergy

end HodgeProofHP
LEAN

lake env lean "$target"
lake build HodgeProofHP.Stage4ThetaHankelBasisEnergy

printf '%s\n' 'PASS: Stage4ThetaHankelBasisEnergy'
