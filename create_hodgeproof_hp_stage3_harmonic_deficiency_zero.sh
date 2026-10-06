#!/usr/bin/env bash
set -euo pipefail

mkdir -p HodgeProofHP

cat > HodgeProofHP/Stage3HarmonicDeficiencyZero.lean <<'LEAN'
import HodgeProofHP.Stage3HermiteAdjointNoNonrealEigen

/-!
The harmonic core adjoint has trivial deficiency spaces
at the eigenvalues I and -I.
-/

namespace HodgeProofHP

theorem hpHarmonicAdjoint_pos_I_eigen_eq_zero
    (f : HPHarmonicCoreOperator.adjoint.domain)
    (hf : HPHarmonicCoreOperator.adjoint.toFun f =
      Complex.I • (f : HPSpace)) :
    (f : HPSpace) = 0 := by
  exact hpHarmonicAdjoint_nonreal_eigen_eq_zero
    Complex.I (by simp) f hf

theorem hpHarmonicAdjoint_neg_I_eigen_eq_zero
    (f : HPHarmonicCoreOperator.adjoint.domain)
    (hf : HPHarmonicCoreOperator.adjoint.toFun f =
      (-Complex.I) • (f : HPSpace)) :
    (f : HPSpace) = 0 := by
  exact hpHarmonicAdjoint_nonreal_eigen_eq_zero
    (-Complex.I) (by simp) f hf

#print axioms hpHarmonicAdjoint_pos_I_eigen_eq_zero
#print axioms hpHarmonicAdjoint_neg_I_eigen_eq_zero

end HodgeProofHP
LEAN

lake env lean HodgeProofHP/Stage3HarmonicDeficiencyZero.lean
lake build HodgeProofHP.Stage3HarmonicDeficiencyZero

python - <<'PY'
from pathlib import Path

names = [
    "Stage3SelfAdjointApiAudit.lean",
    "Stage3ClosureSymmetric.lean",
    "Stage3CoreFormalAdjointClosure.lean",
]
for name in names:
    path = Path("HodgeProofHP") / name
    print(f"\n=== {path} ===")
    if path.exists():
        print(path.read_text(encoding="utf-8"))
    else:
        print("File not found")
PY
