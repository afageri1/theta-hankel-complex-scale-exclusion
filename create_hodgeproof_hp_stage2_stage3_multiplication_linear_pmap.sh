#!/usr/bin/env bash
set -euo pipefail

file="HodgeProofHP/Stage2MultiplicationLinearPMap.lean"

if [[ ! -f HodgeProofHP/Stage2MultiplicationDomainSubmodule.lean ]]; then
  echo "STOP: run from the hodgeproof-hp repository root."
  exit 1
fi

if [[ -e "$file" ]]; then
  echo "STOP: $file already exists; no file was replaced."
  exit 1
fi

cat > "$file" <<'LEAN'
import HodgeProofHP.Stage2MultiplicationDomainSubmodule

/-!
HP.2.3: coordinate multiplication as a partial complex-linear map
on its maximal L² domain.
-/

namespace HodgeProofHP

private theorem hp_mul_rep_add_for_map (f g : HPSpace) :
    hpCoordinateMulRepresentative (f + g) =ᵐ[MeasureTheory.volume]
      (hpCoordinateMulRepresentative f + hpCoordinateMulRepresentative g) := by
  filter_upwards [MeasureTheory.Lp.coeFn_add f g] with x hx
  simp only [hpCoordinateMulRepresentative, Pi.add_apply] at *
  rw [hx]
  ring

private theorem hp_mul_rep_smul_for_map (c : ℂ) (f : HPSpace) :
    hpCoordinateMulRepresentative (c • f) =ᵐ[MeasureTheory.volume]
      c • hpCoordinateMulRepresentative f := by
  filter_upwards [MeasureTheory.Lp.coeFn_smul c f] with x hx
  simp only [hpCoordinateMulRepresentative, Pi.smul_apply] at *
  rw [hx]
  simp only [smul_eq_mul]
  ring

/-- The L² value of coordinate multiplication on an element of its domain. -/
private noncomputable def hpMulValue
    (f : HPMultiplicationDomain) : HPSpace :=
  MeasureTheory.MemLp.toLp (hpCoordinateMulRepresentative (f : HPSpace))
    (by exact f.property)

private theorem hpMulValue_add
    (f g : HPMultiplicationDomain) :
    hpMulValue (f + g) = hpMulValue f + hpMulValue g := by
  have hf : MeasureTheory.MemLp
      (hpCoordinateMulRepresentative (f : HPSpace))
      2 MeasureTheory.volume := f.property
  have hg : MeasureTheory.MemLp
      (hpCoordinateMulRepresentative (g : HPSpace))
      2 MeasureTheory.volume := g.property
  have hfg : MeasureTheory.MemLp
      (hpCoordinateMulRepresentative ((f : HPSpace) + (g : HPSpace)))
      2 MeasureTheory.volume := (f + g).property
  change MeasureTheory.MemLp.toLp
      (hpCoordinateMulRepresentative ((f : HPSpace) + (g : HPSpace))) hfg =
    MeasureTheory.MemLp.toLp
      (hpCoordinateMulRepresentative (f : HPSpace)) hf +
    MeasureTheory.MemLp.toLp
      (hpCoordinateMulRepresentative (g : HPSpace)) hg
  exact
    (MeasureTheory.MemLp.toLp_congr hfg (hf.add hg)
      (hp_mul_rep_add_for_map (f : HPSpace) (g : HPSpace))).trans
      (MeasureTheory.MemLp.toLp_add hf hg)

private theorem hpMulValue_smul
    (c : ℂ) (f : HPMultiplicationDomain) :
    hpMulValue (c • f) = c • hpMulValue f := by
  have hf : MeasureTheory.MemLp
      (hpCoordinateMulRepresentative (f : HPSpace))
      2 MeasureTheory.volume := f.property
  have hcf : MeasureTheory.MemLp
      (hpCoordinateMulRepresentative (c • (f : HPSpace)))
      2 MeasureTheory.volume := (c • f).property
  change MeasureTheory.MemLp.toLp
      (hpCoordinateMulRepresentative (c • (f : HPSpace))) hcf =
    c • MeasureTheory.MemLp.toLp
      (hpCoordinateMulRepresentative (f : HPSpace)) hf
  exact
    (MeasureTheory.MemLp.toLp_congr hcf (hf.const_smul c)
      (hp_mul_rep_smul_for_map c (f : HPSpace))).trans
      (MeasureTheory.MemLp.toLp_const_smul c hf)

/-- Multiplication by the real coordinate, defined precisely on its maximal L² domain. -/
noncomputable def HPMultiplicationOperator :
    LinearPMap (RingHom.id ℂ) HPSpace HPSpace where
  domain := HPMultiplicationDomain
  toFun :=
    { toFun := hpMulValue
      map_add' := hpMulValue_add
      map_smul' := hpMulValue_smul }

#check HPMultiplicationOperator
#print axioms HPMultiplicationOperator

end HodgeProofHP
LEAN

lake env lean "$file"
lake build HodgeProofHP.Stage2MultiplicationLinearPMap
