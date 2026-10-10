#!/usr/bin/env bash
set -euo pipefail

mkdir -p HodgeProofHP

cat > HodgeProofHP/Stage3HarmonicSpectralPackage.lean <<'LEAN'
import HodgeProofHP.Stage3HarmonicFullSpectrum

/-!
# Verified harmonic spectral package

Collect self-adjointness, the orthonormal Hermite family, the full
spectrum, and compactness of unit imaginary resolvents.

No correspondence with the Riemann Xi function is asserted here.
-/

noncomputable section

namespace HodgeProofHP

theorem hpHarmonic_spectral_package :
    HPHarmonicClosure.adjoint = HPHarmonicClosure ∧
    Orthonormal ℂ hpHermiteNormalizedL2 ∧
    hpHarmonicClosureSpectrum =
      Set.range (fun n : ℕ => 2 * (n : ℂ) + 1) ∧
    (∀ (c : ℂ) (hcIm : c.im ≠ 0) (hcRe : c.re = 0)
        (hcNorm : ‖c‖ = 1),
      IsCompactOperator
        (hpHarmonicUnitImaginaryResolvent c hcIm hcRe hcNorm)) := by
  refine ⟨hpHarmonicClosure_adjoint_eq_self,
    hpHermiteNormalizedL2_orthonormal,
    hpHarmonicClosure_spectrum_eq_hermite_range, ?_⟩
  intro c hcIm hcRe hcNorm
  exact hpHarmonicUnitImaginaryResolvent_isCompact c hcIm hcRe hcNorm

end HodgeProofHP

#check HodgeProofHP.hpHermiteHilbertBasis
#check HodgeProofHP.hpHarmonicGeneralResolvent
#check HodgeProofHP.hpHarmonicGeneralSolution_equation
#check HodgeProofHP.hpHarmonicGeneralResolvent_left_inverse
#check HodgeProofHP.hpHarmonicGeneralResolvent_isCompact
#print axioms HodgeProofHP.hpHarmonic_spectral_package
LEAN

lake build HodgeProofHP.Stage3HarmonicFullSpectrum
lake env lean HodgeProofHP/Stage3HarmonicSpectralPackage.lean
lake build HodgeProofHP.Stage3HarmonicSpectralPackage

python - <<'PY'
from pathlib import Path
import re
import subprocess

root = Path(".")
report = Path("stage3_xi_bridge_source_audit.txt")

pattern = re.compile(
    r"Riemann|riemann|Ξ|ζ|Zeta|zeta|"
    r"XiCorrespond|xiCorrespond|XiFunction|xiFunction|"
    r"CompletedXi|completedXi|HilbertPolya|HilbertPólya|"
    r"\b(?:hp|HP)?Xi\w*"
)

result = subprocess.run(
    ["rg", "--files", "--glob", "*.lean",
     "--glob", "!**/.lake/**", "--glob", "!**/.git/**"],
    check=True, capture_output=True, text=True, encoding="utf-8"
)

matches = []
for name in sorted(result.stdout.splitlines()):
    path = root / name
    content = path.read_bytes().decode("utf-8-sig")
    lines = content.splitlines()
    hits = [
        (number, line)
        for number, line in enumerate(lines, 1)
        if pattern.search(line)
    ]
    if hits or pattern.search(path.stem):
        matches.append((path, lines, hits))

output = [
    "STAGE 3: XI BRIDGE SOURCE INVENTORY",
    "This report locates candidate sources; it does not verify a correspondence.",
    "",
    "PROJECT VERSION",
]

for name in ("lean-toolchain", "lakefile.lean", "lakefile.toml"):
    path = root / name
    if path.is_file():
        output.extend([
            f"--- {name} ---",
            path.read_bytes().decode("utf-8-sig"),
        ])

output.extend(["", f"CANDIDATE FILES: {len(matches)}"])
for path, _, hits in matches:
    output.append(f"{path.as_posix()} ({len(hits)} matching lines)")

if not matches:
    output.append(
        "No Xi/Riemann source matched the inventory patterns in this checkout."
    )

for path, lines, hits in matches[:12]:
    output.extend(["", f"--- SOURCE: {path.as_posix()} ---"])
    if len(lines) <= 240:
        output.extend(f"{i}: {line}" for i, line in enumerate(lines, 1))
    else:
        output.append("Selected context around matching lines:")
        selected = set()
        for number, _ in hits[:15]:
            selected.update(
                range(max(1, number - 4), min(len(lines), number + 14) + 1)
            )
        for number in sorted(selected):
            output.append(f"{number}: {lines[number - 1]}")
        output.append(
            f"File has {len(lines)} lines; this is a partial source excerpt."
        )

if len(matches) > 12:
    output.append("Source excerpts limited to the first 12 candidate files.")

report.write_text("\n".join(output) + "\n", encoding="utf-8")
print("\n".join(output))
print(f"\nREPORT: {report}")
PY
