#!/usr/bin/env python3
"""List modules outside the three paper targets' project import closure."""
from pathlib import Path
import re

base = Path("HodgeProofHP")
imports = {}
for path in base.rglob("*.lean"):
    module = ".".join(path.with_suffix("").parts)
    imports[module] = re.findall(r"^import\s+(HodgeProofHP\.\S+)",
                                 path.read_text(encoding="utf-8"), re.M)
targets = ["HodgeProofHP.Stage4ThetaComplexScaledObstructionAudit",
           "HodgeProofHP.Stage5ThetaJensenQuadraticComplexRoots",
           "HodgeProofHP.Stage6ThetaJensenRiemannHypothesisEquivalence"]
used, stack = set(), list(targets)
while stack:
    module = stack.pop()
    if module not in used:
        if module not in imports:
            raise SystemExit("Missing project module: " + module)
        used.add(module)
        stack.extend(imports[module])
for module in sorted(set(imports) - used):
    print(module.replace(".", "/") + ".lean")
