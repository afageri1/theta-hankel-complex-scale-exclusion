#!/usr/bin/env bash
set -euo pipefail

file=HodgeProofHP/Stage3GaussianGroundApi.lean
cp "$file" "$file.before_l2"

python - <<'PY'
from pathlib import Path

path = Path("HodgeProofHP/Stage3GaussianGroundApi.lean")
source = path.read_text(encoding="utf-8")

old = "private noncomputable def hpGaussianGroundFunction"
if source.count(old) != 1:
    raise SystemExit("STOP: Gaussian definition not found exactly once")
source = source.replace(old, "noncomputable def hpGaussianGroundFunction", 1)

anchor = "#check Polynomial.deriv_gaussian_eq_hermite_mul_gaussian"
if source.count(anchor) != 1 or "theorem hpGaussianGroundFunction_memLp" in source:
    raise SystemExit("STOP: insertion point missing or theorem already present")

addition = """theorem hpGaussianGroundFunction_memLp :
    MeasureTheory.MemLp hpGaussianGroundFunction 2 MeasureTheory.volume := by
  have hmeas : MeasureTheory.AEStronglyMeasurable
      hpGaussianGroundFunction MeasureTheory.volume :=
    (show Continuous hpGaussianGroundFunction by
      unfold hpGaussianGroundFunction
      fun_prop).aestronglyMeasurable
  apply (MeasureTheory.memLp_two_iff_integrable_sq_norm hmeas).2
  have hsq (x : ℝ) :
      ‖hpGaussianGroundFunction x‖ ^ 2 = Real.exp (-(1 : ℝ) * x ^ 2) := by
    rw [hpGaussianGroundFunction, norm_cexp_neg_mul_sq]
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num <;> ring
  simpa only [hsq] using
    (integrable_exp_neg_mul_sq (b := (1 : ℝ)) (by norm_num))

#print axioms hpGaussianGroundFunction_memLp

"""
path.write_text(source.replace(anchor, addition + anchor, 1), encoding="utf-8")
PY

lake env lean "$file"
lake build HodgeProofHP.Stage3GaussianGroundApi
