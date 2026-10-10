#!/usr/bin/env bash
set -euo pipefail

lake build HodgeProofHP.Stage4ThetaHankelSpectralFamily

target="HodgeProofHP/Stage4ThetaHankelSpectralCompleteness.lean"

if [ -f "$target" ]; then
  cp -p "$target" "$target.before_update_$(date +%Y%m%d_%H%M%S)"
fi

cat > "$target" <<'LEAN'
import HodgeProofHP.Stage4ThetaHankelSpectralFamily
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Topology.Algebra.Module.Basic

/-!
Completeness of the collected eigenspace bases.
The zero eigenspace is included.
-/

namespace HodgeProofHP

set_option maxHeartbeats 2000000 in
-- Elaborating the dependent eigenspace bases requires additional heartbeats.
theorem hpThetaHankelSpectralFamily_inner_eq_zero_on_eigenspace
    (x : HPThetaHankelSpace)
    (hx : ∀ i : HPThetaHankelSpectralIndex,
      inner ℂ x (hpThetaHankelSpectralFamily i) = 0)
    (ev : ℂ) (y : ↥(hpThetaHankelEigenspace ev)) :
    inner ℂ x (y : HPThetaHankelSpace) = 0 := by
  let L : ↥(hpThetaHankelEigenspace ev) →L[ℂ] ℂ :=
    (innerSL ℂ x).comp
      (hpThetaHankelEigenspace ev).subtypeₗᵢ.toContinuousLinearMap
  have hspan :
      Submodule.span ℂ
          (Set.range ⇑(hpThetaHankelEigenspaceBasis ev)) ≤
        L.toLinearMap.ker := by
    apply Submodule.span_le.mpr
    rintro z ⟨i, rfl⟩
    change inner ℂ x
      ((hpThetaHankelEigenspaceBasis ev i) : HPThetaHankelSpace) = 0
    exact hx ⟨ev, i⟩
  have hclosed :
      IsClosed
        (L.toLinearMap.ker :
          Set ↥(hpThetaHankelEigenspace ev)) := by
    change IsClosed
      {z : ↥(hpThetaHankelEigenspace ev) | L z = 0}
    exact isClosed_eq L.continuous continuous_const
  have hclosure :=
    Submodule.topologicalClosure_minimal
      (Submodule.span ℂ
        (Set.range ⇑(hpThetaHankelEigenspaceBasis ev)))
      hspan hclosed
  rw [(hpThetaHankelEigenspaceBasis ev).dense_span] at hclosure
  have hy :
      y ∈ L.toLinearMap.ker :=
    hclosure (Submodule.mem_top : y ∈
      (⊤ : Submodule ℂ ↥(hpThetaHankelEigenspace ev)))
  change inner ℂ x (y : HPThetaHankelSpace) = 0 at hy
  exact hy

set_option maxHeartbeats 2000000 in
-- The proof passes between the collected family and dependent eigenspaces.
theorem hpThetaHankelSpectralFamily_orthogonalComplement_eq_bot :
    (Submodule.span ℂ
      (Set.range hpThetaHankelSpectralFamily))ᗮ = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro x hx
  have hfamily :
      ∀ i : HPThetaHankelSpectralIndex,
        inner ℂ x (hpThetaHankelSpectralFamily i) = 0 := by
    intro i
    exact
      (Submodule.mem_orthogonal'
        (Submodule.span ℂ
          (Set.range hpThetaHankelSpectralFamily)) x).mp hx
        (hpThetaHankelSpectralFamily i)
        (Submodule.subset_span ⟨i, rfl⟩)
  have heigenspaces :
      ∀ ev : ℂ, x ∈ (hpThetaHankelEigenspace ev)ᗮ := by
    intro ev
    apply (Submodule.mem_orthogonal'
      (hpThetaHankelEigenspace ev) x).mpr
    intro y hy
    exact hpThetaHankelSpectralFamily_inner_eq_zero_on_eigenspace
      x hfamily ev ⟨y, hy⟩
  have htotal :
      x ∈ (⨆ ev : ℂ, hpThetaHankelEigenspace ev)ᗮ := by
    rw [← Submodule.iInf_orthogonal]
    simpa using heigenspaces
  change x ∈
    (⨆ ev : ℂ,
      Module.End.eigenspace
        hpThetaHankelAdjointSquare.toLinearMap ev)ᗮ at htotal
  rw [hpThetaHankelAdjointSquare_eigenspaces_orthogonalComplement_eq_bot]
    at htotal
  exact htotal

#print axioms hpThetaHankelSpectralFamily_inner_eq_zero_on_eigenspace
#print axioms hpThetaHankelSpectralFamily_orthogonalComplement_eq_bot

end HodgeProofHP
LEAN

lake env lean "$target"
lake build HodgeProofHP.Stage4ThetaHankelSpectralCompleteness

printf '%s\n' 'PASS: Stage4ThetaHankelSpectralCompleteness'
