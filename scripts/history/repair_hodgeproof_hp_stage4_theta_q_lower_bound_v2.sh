#!/usr/bin/env bash
set -euo pipefail

python - <<'PY'
from pathlib import Path
from datetime import datetime
import shutil

paths = [
    Path("HodgeProofHP/Stage4ThetaHankelQLowerBound.lean"),
    Path("create_hodgeproof_hp_stage4_theta_q_lower_bound.sh"),
]

start = "private theorem hpThetaQ_repr_norm_sq_hasSum"
end = "private theorem hpThetaQ_adjointSquare_inner_swap"

replacement = """private theorem hpThetaQ_repr_norm_sq_hasSum
    (f : HPThetaHankelSpace) :
    HasSum
      (fun i : HPThetaHankelSpectralIndex =>
        ‖(hpThetaHankelSpectralBasis.repr f) i‖ ^ 2)
      (‖f‖ ^ 2) := by
  have h :=
    (lp.hasSum_inner (𝕜 := ℂ)
      (hpThetaHankelSpectralBasis.repr f)
      (hpThetaHankelSpectralBasis.repr f)).map
        Complex.reCLM Complex.reCLM.continuous
  change HasSum
    (fun i : HPThetaHankelSpectralIndex =>
      RCLike.re (inner ℂ
        ((hpThetaHankelSpectralBasis.repr f) i)
        ((hpThetaHankelSpectralBasis.repr f) i)))
    (RCLike.re (inner ℂ
      (hpThetaHankelSpectralBasis.repr f)
      (hpThetaHankelSpectralBasis.repr f))) at h
  simpa only [inner_self_eq_norm_sq,
    LinearIsometryEquiv.norm_map] using h

"""

old = """  rw [inner_smul_left_eq_smul]
  change
    (i.1.re : ℂ) * inner ℂ (hpThetaHankelSpectralBasis i) f =
      (i.1.re : ℂ) * inner ℂ (hpThetaHankelSpectralBasis i) f
  rfl"""

new = """  change
    inner ℂ ((i.1.re : ℂ) • hpThetaHankelSpectralBasis i) f =
      (i.1.re : ℂ) * inner ℂ (hpThetaHankelSpectralBasis i) f
  rw [inner_smul_left]
  have hc :
      (starRingEnd ℂ) (i.1.re : ℂ) = (i.1.re : ℂ) := by
    change star (Complex.ofReal i.1.re) = Complex.ofReal i.1.re
    simp
  rw [hc]"""

prepared = []
for p in paths:
    if not p.is_file():
        raise SystemExit(f"STOP: missing {p}")
    raw = p.read_bytes()
    text = raw.decode("utf-8").replace("\r\n", "\n")
    for marker in [start, end, old]:
        if text.count(marker) != 1:
            raise SystemExit(f"STOP: unexpected source structure: {p}")
    a = text.index(start)
    b = text.index(end, a)
    fixed = text[:a] + replacement + text[b:]
    fixed = fixed.replace(old, new)
    newline = "\r\n" if b"\r\n" in raw else "\n"
    prepared.append((p, fixed.replace("\n", newline).encode("utf-8")))

stamp = datetime.now().strftime("%Y%m%d_%H%M%S_%f")
for p, data in prepared:
    backup = p.with_name(p.name + ".before_q_v2_" + stamp)
    shutil.copy2(p, backup)
    p.write_bytes(data)
    print(f"BACKUP: {backup}")
    print(f"REPAIRED: {p}")
PY

mkdir -p stage4_fourth_certificate_build_logs
log="stage4_fourth_certificate_build_logs/q_lower_bound_repair_v2.log"

if lake build HodgeProofHP.Stage4ThetaHankelQLowerBound >"$log" 2>&1; then
    tail -n 55 "$log"
    echo "PASS: Stage4ThetaHankelQLowerBound"
else
    tail -n 100 "$log"
    echo "STOP: build failed; log: $log"
    exit 1
fi
