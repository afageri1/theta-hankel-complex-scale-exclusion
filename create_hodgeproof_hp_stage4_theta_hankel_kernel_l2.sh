#!/usr/bin/env bash
set -euo pipefail

if [[ ! -f lakefile.lean && ! -f lakefile.toml ]]; then
  echo "STOP: run from the hodgeproof-hp project root."
  exit 1
fi

lake build HodgeProofHP.Stage4ThetaHankelSquareFiniteness

target="HodgeProofHP/Stage4ThetaHankelKernelL2.lean"
mkdir -p HodgeProofHP

if [[ -f "$target" ]]; then
  backup="${target}.before_create_$(date +%Y%m%d_%H%M%S)_$$"
  cp -p "$target" "$backup"
  echo "BACKUP: $backup"
fi

cat > "$target" <<'LEAN'
import HodgeProofHP.Stage4ThetaHankelSquareFiniteness
import Mathlib.MeasureTheory.Function.L2Space

/-!
The half-line Hankel kernel belongs to L2 on the product measure.
Its row and column sections belong to L2 almost everywhere.
-/

noncomputable section

namespace HodgeProofHP

open MeasureTheory
open scoped ENNReal

def hpThetaHankelMeasure : Measure ℝ :=
  volume.restrict (Set.Ioi (0 : ℝ))

instance hpThetaHankelMeasure_sFinite : SFinite hpThetaHankelMeasure := by
  unfold hpThetaHankelMeasure
  infer_instance

abbrev HPThetaHankelSpace :=
  Lp ℂ 2 hpThetaHankelMeasure

example : CompleteSpace HPThetaHankelSpace := inferInstance
example : InnerProductSpace ℂ HPThetaHankelSpace := inferInstance

theorem hpThetaHankelKernel_memLp :
    MemLp
      (fun p : ℝ × ℝ => hpThetaHankelKernel p.1 p.2)
      2 (hpThetaHankelMeasure.prod hpThetaHankelMeasure) := by
  apply (memLp_two_iff_integrable_sq_norm
    hpThetaHankelKernel_continuous.aestronglyMeasurable).2
  simpa only [hpThetaHankelMeasure]
    using hpThetaHankelKernel_norm_sq_integrable

theorem hpThetaHankelKernel_row_memLp_ae :
    ∀ᵐ x ∂hpThetaHankelMeasure,
      MemLp (fun y : ℝ => hpThetaHankelKernel x y)
        2 hpThetaHankelMeasure := by
  have hsq :
      Integrable
        (fun p : ℝ × ℝ => ‖hpThetaHankelKernel p.1 p.2‖ ^ 2)
        (hpThetaHankelMeasure.prod hpThetaHankelMeasure) := by
    simpa only [hpThetaHankelMeasure]
      using hpThetaHankelKernel_norm_sq_integrable
  filter_upwards [hsq.prod_right_ae] with x hx
  have hcont :
      Continuous (fun y : ℝ => hpThetaHankelKernel x y) :=
    hpThetaHankelKernel_continuous.comp
      (continuous_const.prodMk continuous_id)
  exact (memLp_two_iff_integrable_sq_norm
    hcont.aestronglyMeasurable).2 hx

theorem hpThetaHankelKernel_column_memLp_ae :
    ∀ᵐ y ∂hpThetaHankelMeasure,
      MemLp (fun x : ℝ => hpThetaHankelKernel x y)
        2 hpThetaHankelMeasure := by
  have hsq :
      Integrable
        (fun p : ℝ × ℝ => ‖hpThetaHankelKernel p.1 p.2‖ ^ 2)
        (hpThetaHankelMeasure.prod hpThetaHankelMeasure) := by
    simpa only [hpThetaHankelMeasure]
      using hpThetaHankelKernel_norm_sq_integrable
  filter_upwards [hsq.prod_left_ae] with y hy
  have hcont :
      Continuous (fun x : ℝ => hpThetaHankelKernel x y) :=
    hpThetaHankelKernel_continuous.comp
      (continuous_id.prodMk continuous_const)
  exact (memLp_two_iff_integrable_sq_norm
    hcont.aestronglyMeasurable).2 hy

def hpThetaHankelKernelL2 :
    Lp ℂ 2 (hpThetaHankelMeasure.prod hpThetaHankelMeasure) :=
  MemLp.toLp
    (fun p : ℝ × ℝ => hpThetaHankelKernel p.1 p.2)
    hpThetaHankelKernel_memLp

#print axioms hpThetaHankelKernel_memLp
#print axioms hpThetaHankelKernel_row_memLp_ae
#print axioms hpThetaHankelKernel_column_memLp_ae
#print axioms hpThetaHankelKernelL2

end HodgeProofHP
LEAN

lake env lean "$target"
lake build HodgeProofHP.Stage4ThetaHankelKernelL2

echo "PASS: Stage4ThetaHankelKernelL2"
