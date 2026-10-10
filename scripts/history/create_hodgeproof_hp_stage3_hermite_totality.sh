#!/usr/bin/env bash
set -euo pipefail

target="HodgeProofHP/Stage3HermiteTotality.lean"

if [ -f "$target" ]; then
  cp "$target" "$target.bak.$(date +%Y%m%d_%H%M%S)"
fi

cat > "$target" <<'LEAN'
import HodgeProofHP.Stage3HermiteDenseSpan

/-!
An L² vector vanishes if all its Hermite inner-product coefficients vanish.
-/

noncomputable section

namespace HodgeProofHP

theorem hpHermiteL2_inner_eq_zero_imp_eq_zero
    (v : HPSpace)
    (h : ∀ n : ℕ, inner ℂ v (hpHermiteL2 n) = 0) :
    v = 0 := by
  have hle : hpHermiteL2Span ≤ (innerSL ℂ v).ker := by
    change Submodule.span ℂ (Set.range hpHermiteL2) ≤
      (innerSL ℂ v).ker
    apply Submodule.span_le.mpr
    rintro u ⟨n, rfl⟩
    change inner ℂ v (hpHermiteL2 n) = 0
    exact h n
  apply hpHermiteL2Span_orthogonal_eq_zero v
  apply (Submodule.mem_orthogonal' hpHermiteL2Span v).mpr
  intro u hu
  have hz := hle hu
  change inner ℂ v u = 0 at hz
  exact hz

end HodgeProofHP

#print axioms HodgeProofHP.hpHermiteL2_inner_eq_zero_imp_eq_zero
LEAN

lake env lean "$target"
lake build HodgeProofHP.Stage3HermiteTotality

python - <<'PY'
from pathlib import Path

names = [
    "Stage3HermiteCoreEigen.lean",
    "Stage3DeficiencyRangeOrthogonality.lean",
    "Stage3DeficiencyDenseRangeCriterion.lean",
    "Stage3HarmonicCore.lean",
]

print("\n=== HERМITE AND SHIFTED RANGE LOCAL API ===")
for name in names:
    path = Path("HodgeProofHP") / name
    print(f"\nFILE: {path}")
    if path.exists():
        print(path.read_text(encoding="utf-8"))
    else:
        print("MISSING")
PY
