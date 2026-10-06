#!/usr/bin/env bash
set -euo pipefail

python - <<'PY'
from pathlib import Path
from datetime import datetime

paths = [
    Path("HodgeProofHP/Stage4ThetaHankelSpectralProductPolynomialLimits.lean"),
    Path("create_hodgeproof_hp_stage4_theta_spectral_product_polynomial_limits.sh"),
]

replacements = [
    (
"""      simpa only [hpThetaHankelFiniteSpectralProduct, Finset.prod_empty]
        using (differentiable_const (1 : ℂ))""",
"""      change Differentiable ℂ
        (fun z : ℂ => ∏ i ∈ (∅ : Finset HPThetaHankelSpectralIndex),
          hpThetaHankelSpectralProductFactor i z)
      simpa only [Finset.prod_empty]
        using (differentiable_const (1 : ℂ))"""
    ),
    (
"""      simpa only [hpThetaHankelFiniteSpectralProduct,
        Finset.prod_insert hi] using h""",
"""      change Differentiable ℂ
        (fun z : ℂ => ∏ j ∈ insert i F,
          hpThetaHankelSpectralProductFactor j z)
      simp only [Finset.prod_insert hi]
      change Differentiable ℂ
        (hpThetaHankelSpectralProductFactor i *
          hpThetaHankelFiniteSpectralProduct F)
      exact h"""
    ),
    (
"""  simpa only [hpThetaHankelFiniteSpectralProduct]
    using h.tendstoUniformlyOn""",
"""  change TendstoUniformlyOn
    (fun F : Finset HPThetaHankelSpectralIndex =>
      fun z : ℂ => ∏ i ∈ F,
        hpThetaHankelSpectralProductFactor i z)
    hpThetaHankelSpectralProduct Filter.atTop
    (Metric.closedBall (0 : ℂ) r)
  exact h.tendstoUniformlyOn"""
    ),
]

prepared = []
for path in paths:
    if not path.is_file():
        raise SystemExit(f"STOP: missing {path}")
    original = path.read_bytes()
    text = original.decode("utf-8").replace("\r\n", "\n")
    for old, new in replacements:
        count = text.count(old)
        if count != 1:
            raise SystemExit(
                f"STOP: {path}: expected 1 matching block, found {count}"
            )
        text = text.replace(old, new, 1)
    newline = "\r\n" if b"\r\n" in original else "\n"
    prepared.append((path, original, text.replace("\n", newline).encode("utf-8")))

stamp = datetime.now().strftime("%Y%m%d_%H%M%S_%f")
for path, original, updated in prepared:
    backup = path.with_name(path.name + ".before_repair_" + stamp)
    backup.write_bytes(original)
    path.write_bytes(updated)
    print(f"BACKUP: {backup}")
    print(f"REPAIRED: {path}")
PY

bash create_hodgeproof_hp_stage4_theta_spectral_product_polynomial_limits.sh
