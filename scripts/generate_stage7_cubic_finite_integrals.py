#!/usr/bin/env python3
"""Assemble accepted batch integral and numerical rectangle bounds on (0,1)."""
from pathlib import Path
import argparse
HEADER='''/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
'''
BOUNDS={90:('(-26 / 100 : ℝ)','(-23 / 100 : ℝ)'),55:('(6 / 1000 : ℝ)','(18 / 1000 : ℝ)'),42:('(-19 / 1000 : ℝ)','(-9 / 1000 : ℝ)'),15:('(127 / 1000 : ℝ)','(134 / 1000 : ℝ)')}
def generate(p):
 pre=f'hpThetaJensenCubicNeg{p}'
 helpers=''
 for b in range(80):
  helpers+=f'''
theorem {pre}Batch{b:03}_integral_rectangle_bounds :
    {pre}RectangleLower {b} ≤
      (∫ u : ℝ in Set.Ioo ((({b} : ℕ) : ℝ) / 80) (((({b} : ℕ) : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-{p}) u) ∧
    (∫ u : ℝ in Set.Ioo ((({b} : ℕ) : ℝ) / 80) (((({b} : ℕ) : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-{p}) u) ≤
        {pre}RectangleUpper {b} := by
  simpa only [{pre}RectangleLower, {pre}RectangleUpper,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using
    hpThetaJensenCubicBatch{b:03}Neg{p}_integral_bounds
'''
 src=HEADER+f'''import HodgeProofHP.Stage7ThetaJensenCubicBatchIntegralsNeg{p}
import HodgeProofHP.Stage7ThetaJensenCubicRectanglesNeg{p}

/-! Bounds on the finite weighted integral only. The tail and full evaluation
signs remain separate obligations. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

{helpers}
theorem {pre}_batchIntegral_rectangle_bounds (b : Fin 80) :
    {pre}RectangleLower b.val ≤
      (∫ u : ℝ in Set.Ioo ((b.val : ℝ) / 80) (((b.val : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-{p}) u) ∧
    (∫ u : ℝ in Set.Ioo ((b.val : ℝ) / 80) (((b.val : ℝ) + 1) / 80),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-{p}) u) ≤
        {pre}RectangleUpper b.val := by
  fin_cases b
'''
 for b in range(80):
  src+=f'  · exact {pre}Batch{b:03}_integral_rectangle_bounds\n'
 src+=f'''
theorem {pre}_batchIntegral_sum :
    (∑ b ∈ Finset.range 80,
      ∫ u : ℝ in Set.Ioo ((b : ℝ) / 80) (((b : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-{p}) u) =
      ∫ u : ℝ in Set.Ioo 0 1,
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-{p}) u := by
  have h := hpThetaJensenCubic_uniformCellIntegral_sum (-{p}) 80 0 (1 / 80)
    (by norm_num) (by norm_num)
  have hc (b : ℕ) :
      Set.Ioo (0 + (b : ℝ) * (1 / 80))
        (0 + ((b + 1 : ℕ) : ℝ) * (1 / 80)) =
      Set.Ioo ((b : ℝ) / 80) (((b : ℝ) + 1) / 80) := by
    congr 1 <;> push_cast <;> ring
  simp_rw [hc] at h
  norm_num only [Nat.cast_ofNat, zero_add] at h
  exact h

theorem {pre}_finiteIntegral_bounds :
    {BOUNDS[p][0]} ≤
      (∫ u : ℝ in Set.Ioo 0 1,
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-{p}) u) ∧
    (∫ u : ℝ in Set.Ioo 0 1,
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-{p}) u) ≤
        {BOUNDS[p][1]} := by
  have hl : (∑ b ∈ Finset.range 80, {pre}RectangleLower b) ≤
      ∑ b ∈ Finset.range 80,
        ∫ u : ℝ in Set.Ioo ((b : ℝ) / 80) (((b : ℝ) + 1) / 80),
          hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-{p}) u := by
    apply Finset.sum_le_sum
    intro b hb
    exact ({pre}_batchIntegral_rectangle_bounds ⟨b, Finset.mem_range.mp hb⟩).1
  have hu : (∑ b ∈ Finset.range 80,
      ∫ u : ℝ in Set.Ioo ((b : ℝ) / 80) (((b : ℝ) + 1) / 80),
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight (-{p}) u) ≤
      ∑ b ∈ Finset.range 80, {pre}RectangleUpper b := by
    apply Finset.sum_le_sum
    intro b hb
    exact ({pre}_batchIntegral_rectangle_bounds ⟨b, Finset.mem_range.mp hb⟩).2
  rw [{pre}_batchIntegral_sum] at hl hu
  constructor
  · convert le_trans {pre}_rectangle_lower_numeric hl using 1 <;> norm_num
  · convert le_trans hu {pre}_rectangle_upper_numeric using 1 <;> norm_num

#print axioms {pre}_batchIntegral_rectangle_bounds
#print axioms {pre}_batchIntegral_sum
#print axioms {pre}_finiteIntegral_bounds
end HodgeProofHP
'''
 return src
if __name__=='__main__':
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('--output-dir',type=Path,default=Path('HodgeProofHP'))
 args=ap.parse_args();args.output_dir.mkdir(parents=True,exist_ok=True)
 for p in BOUNDS:
  path=args.output_dir/f'Stage7ThetaJensenCubicFiniteIntegralNeg{p}.lean'
  path.write_text(generate(p),encoding='utf-8');print(path)
