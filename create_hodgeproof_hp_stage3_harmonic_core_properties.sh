#!/usr/bin/env bash
set -euo pipefail

file=HodgeProofHP/Stage3HarmonicCoreProperties.lean
if [[ -e "$file" ]]; then
  echo "File already exists: $file" >&2
  exit 1
fi

cat > "$file" <<'LEAN'
import HodgeProofHP.Stage3HarmonicCore

/-! Injectivity and density of the Schwartz realization in complex L². -/

namespace HodgeProofHP

theorem hpSchwartzToL2_injective :
    Function.Injective hpSchwartzToL2 := by
  change Function.Injective
    (fun f : SchwartzMap ℝ ℂ => f.toLp 2 MeasureTheory.volume)
  exact SchwartzMap.injective_toLp 2 MeasureTheory.volume

theorem hpSchwartzDomain_dense :
    Dense (HPSchwartzDomain : Set HPSpace) := by
  change DenseRange (hpSchwartzToL2 : SchwartzMap ℝ ℂ → HPSpace)
  change DenseRange
    ⇑(SchwartzMap.toLpCLM ℝ ℂ 2 MeasureTheory.volume)
  exact SchwartzMap.denseRange_toLpCLM
    (E := ℝ) (F := ℂ) (p := 2)
    (μ := MeasureTheory.volume) (by norm_num)

#print axioms hpSchwartzToL2_injective
#print axioms hpSchwartzDomain_dense

end HodgeProofHP
LEAN

lake build HodgeProofHP.Stage3HarmonicCoreProperties
