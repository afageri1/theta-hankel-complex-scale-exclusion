#!/usr/bin/env bash
set -euo pipefail

python - <<'PY'
from pathlib import Path
from datetime import datetime
import shutil

paths = [
    Path("HodgeProofHP/Stage4ThetaHankelFourthRealInvariant.lean"),
    Path("create_hodgeproof_hp_stage4_theta_hankel_fourth_real_invariant.sh"),
]

patches = [
    (
        """  simpa only [Complex.reCLM_apply,
""",
        """  simpa only [Function.comp_def, Complex.reCLM_apply,
""",
    ),
    (
        """    simpa only [Complex.imCLM_apply,
""",
        """    simpa only [Function.comp_def, Complex.imCLM_apply,
""",
    ),
    (
        """  have h :=
    hpThetaHankelScaledSpectralProduct_eq_normalizedXi_invariant_necessary
      c hmatch
  rw [hpThetaHankelSpectralSquareSum_eq_cast_energy] at h
  have hre := congrArg Complex.re h
  simpa [hpThetaNormalizedXiFourthTraceCoefficient,
    pow_two, Complex.mul_re, Complex.mul_im] using hre
""",
        """  let r : ℝ :=
    -(deriv (deriv hpRiemannXiCritical) 0).re /
      (2 * (hpRiemannXiCritical 0).re)
  have h :=
    hpThetaHankelScaledSpectralProduct_eq_normalizedXi_invariant_necessary
      c hmatch
  change
    (r : ℂ) ^ 2 *
        ((hpThetaFirstTraceEnergy : ℂ) ^ 2 -
          hpThetaHankelSpectralSquareSum) =
      (hpThetaFirstTraceEnergy : ℂ) ^ 2 *
        (hpThetaIteratedComplexDeriv 4 hpThetaNormalizedXi 0 / 12) at h
  rw [hpThetaHankelSpectralSquareSum_eq_cast_energy] at h
  have hre := congrArg Complex.re h
  change
    r ^ 2 * (hpThetaFirstTraceEnergy ^ 2 -
      hpThetaHankelSpectralSquareEnergy) =
        hpThetaFirstTraceEnergy ^ 2 *
          hpThetaNormalizedXiFourthTraceCoefficient
  simpa only [hpThetaNormalizedXiFourthTraceCoefficient,
    pow_two, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im,
    Complex.sub_re, Complex.sub_im,
    mul_zero, zero_mul, sub_zero, add_zero, zero_add] using hre
""",
    ),
]

updates = []
for path in paths:
    if not path.is_file():
        raise SystemExit(f"STOP: missing file: {path}")
    raw = path.read_bytes()
    newline = "\r\n" if b"\r\n" in raw else "\n"
    source = raw.decode("utf-8").replace("\r\n", "\n")
    for number, (old, new) in enumerate(patches, 1):
        count = source.count(old)
        if count != 1:
            raise SystemExit(
                f"STOP: {path}: patch {number}: "
                f"expected 1 occurrence, found {count}"
            )
        source = source.replace(old, new, 1)
    updates.append((path, source.replace("\n", newline).encode("utf-8")))

stamp = datetime.now().strftime("%Y%m%d_%H%M%S_%f")
for path, revised in updates:
    backup = Path(str(path) + ".before_repair_" + stamp)
    shutil.copy2(path, backup)
    print(f"BACKUP: {backup}")
    path.write_bytes(revised)
    print(f"REPAIRED: {path}")
PY

bash create_hodgeproof_hp_stage4_theta_hankel_fourth_real_invariant.sh
