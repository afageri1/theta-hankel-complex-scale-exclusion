#!/usr/bin/env bash
set -euo pipefail

python - <<'PY'
from pathlib import Path
from fractions import Fraction as F
from datetime import datetime
import csv

root = Path("HodgeProofHP")
table = Path("stage4_theta_energy_upper_cells.csv")
stamp = datetime.now().strftime("%Y%m%d_%H%M%S_%f")

with table.open(encoding="utf-8", newline="") as f:
    rows = list(csv.DictReader(f))
if len(rows) != 800:
    raise SystemExit("STOP: expected 800 certificate rows")

cells = []
for i, row in enumerate(rows):
    if int(row["i"]) != i:
        raise SystemExit("STOP: certificate rows are out of order")
    l, r, H = F(row["l"]), F(row["r"]), F(row["H"])
    if l != F(i, 800) or r != F(i+1, 800) or H < 0:
        raise SystemExit(f"STOP: invalid interval row {i}")
    cells.append((l, r, H))

def lean(x):
    if x.denominator == 1:
        return f"({x.numerator} : ℝ)"
    return f"({x.numerator} / {x.denominator} : ℝ)"

def save(path, text):
    data = text.encode("utf-8")
    if path.exists():
        old = path.read_bytes()
        if old == data:
            print(f"UNCHANGED: {path}")
            return
        backup = path.with_name(path.name + ".before_update_" + stamp)
        backup.write_bytes(old)
        print(f"BACKUP: {backup}")
    path.write_bytes(data)
    print(f"CREATED: {path}")

base = """\
import HodgeProofHP.Stage4ThetaKernelIntervalUpper
import HodgeProofHP.Stage4ThetaHankelSquareIntegrability
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Convert pointwise kernel certificates into interval energy bounds. -/

noncomputable section

open MeasureTheory

namespace HodgeProofHP

def hpThetaEnergyUpperIntegrand (u : ℝ) : ℝ :=
  u * hpRiemannThetaDifferentialKernel u ^ 2

theorem hpThetaEnergyUpperIntegrand_continuous :
    Continuous hpThetaEnergyUpperIntegrand := by
  exact continuous_id.mul
    (hpRiemannThetaDifferentialKernel_continuous.pow 2)

theorem hpThetaEnergyUpperIntegrand_intervalIntegrable (a b : ℝ) :
    IntervalIntegrable hpThetaEnergyUpperIntegrand volume a b :=
  hpThetaEnergyUpperIntegrand_continuous.intervalIntegrable a b

theorem hpThetaEnergyUpper_interval_integral_bound
    (l r H : ℝ)
    (hl : 0 ≤ l)
    (hlr : l ≤ r)
    (hH : 0 ≤ H)
    (hbound : ∀ u ∈ Set.Icc l r,
      hpRiemannThetaDifferentialKernel u ≤ H) :
    (∫ u in l..r, hpThetaEnergyUpperIntegrand u) ≤
      H ^ 2 * (r ^ 2 - l ^ 2) / 2 := by
  have hg :
      IntervalIntegrable (fun u : ℝ => u * H ^ 2) volume l r :=
    (continuous_id.mul continuous_const).intervalIntegrable l r
  have h := intervalIntegral.integral_mono_on hlr
    (hpThetaEnergyUpperIntegrand_intervalIntegrable l r) hg
    (by
      intro u hu
      have hu0 : 0 ≤ u := le_trans hl hu.1
      have hphi0 : 0 ≤ hpRiemannThetaDifferentialKernel u :=
        le_of_lt (hpThetaPhi_pos_on_nonnegative u hu0)
      have hsq :
          hpRiemannThetaDifferentialKernel u ^ 2 ≤ H ^ 2 :=
        pow_le_pow_left₀ hphi0 (hbound u hu) 2
      exact mul_le_mul_of_nonneg_left hsq hu0)
  rw [intervalIntegral.integral_mul_const, integral_id] at h
  convert h using 1 <;> ring

#print axioms hpThetaEnergyUpper_interval_integral_bound

end HodgeProofHP
"""
save(root / "Stage4ThetaEnergyUpperIntegralBase.lean", base)

batch_bounds = []
for b in range(40):
    start, stop = 20*b, 20*b+20
    left, right = F(start, 800), F(stop, 800)
    bound = sum(
        (H**2*(r**2-l**2)/2 for l, r, H in cells[start:stop]),
        F(0),
    )
    batch_bounds.append(bound)
    parts = [
        "import HodgeProofHP.Stage4ThetaEnergyUpperIntegralBase\n",
        f"import HodgeProofHP.Stage4ThetaEnergyUpperCertificateBatch{b:02d}\n\n",
        "/-! Integrate and combine twenty certified interval bounds. -/\n\n",
        "noncomputable section\n\n",
        "namespace HodgeProofHP\n\n",
        "set_option maxHeartbeats 2000000 in\n",
        "-- Combining twenty exact rational integral bounds.\n",
        f"theorem hpThetaEnergyUpper_integral_batch_{b} :\n",
        f"    (∫ u in {lean(left)}..{lean(right)},\n",
        "      hpThetaEnergyUpperIntegrand u) ≤\n",
        f"        {lean(bound)} := by\n",
    ]
    names = []
    for j, i in enumerate(range(start, stop)):
        l, r, H = cells[i]
        names.append(f"h{j}")
        parts.append(f"""\
  have h{j} := hpThetaEnergyUpper_interval_integral_bound
    {lean(l)} {lean(r)} {lean(H)}
    (by norm_num) (by norm_num) (by norm_num)
    (by
      intro u hu
      exact hpThetaEnergyUpper_interval_{i} u
        (by simpa only [zero_div, div_one] using hu.1)
        (by simpa only [zero_div, div_one] using hu.2))
  norm_num at h{j}
""")
    for i in range(start, stop-1):
        l, r, _ = cells[i]
        parts.append(f"""\
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := {lean(l)}) (b := {lean(r)}) (c := {lean(right)})
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
""")
    parts.append("  linarith only [" + ", ".join(names) + "]\n\n")
    parts.append(
        f"#print axioms hpThetaEnergyUpper_integral_batch_{b}\n\n"
        "end HodgeProofHP\n"
    )
    save(
        root / f"Stage4ThetaEnergyUpperIntegralBatch{b:02d}.lean",
        "".join(parts),
    )

total = sum(batch_bounds, F(0))
expected = F(1080380018191215381377, 12800000000000000000000)
if total != expected:
    raise SystemExit("STOP: certificate total differs from the successful run")
assert total < F(169, 2000)

parts = [
    "".join(
        f"import HodgeProofHP.Stage4ThetaEnergyUpperIntegralBatch{b:02d}\n"
        for b in range(40)
    ),
    "\n/-! Certified upper bound for theta energy between zero and one. -/\n\n",
    "noncomputable section\n\nnamespace HodgeProofHP\n\n",
    "set_option maxHeartbeats 2000000 in\n",
    "-- Combining forty previously checked rational batch bounds.\n",
    "theorem hpThetaEnergyUpper_integral_zero_one_le_certificate :\n",
    "    (∫ u in (0 : ℝ)..1, hpThetaEnergyUpperIntegrand u) ≤\n",
    f"      {lean(total)} := by\n",
]
for b in range(40):
    parts.append(f"  have h{b} := hpThetaEnergyUpper_integral_batch_{b}\n")
for b in range(39):
    parts.append(f"""\
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := {lean(F(b,40))}) (b := {lean(F(b+1,40))}) (c := (1 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
""")
parts.append(
    "  linarith only [" + ", ".join(f"h{b}" for b in range(40)) + "]\n\n"
)
parts.append("""\
theorem hpThetaEnergyUpper_integral_zero_one_lt :
    (∫ u in (0 : ℝ)..1,
      u * hpRiemannThetaDifferentialKernel u ^ 2) <
        (169 / 2000 : ℝ) := by
  exact lt_of_le_of_lt
    hpThetaEnergyUpper_integral_zero_one_le_certificate (by norm_num)

#print axioms hpThetaEnergyUpper_integral_zero_one_le_certificate
#print axioms hpThetaEnergyUpper_integral_zero_one_lt

end HodgeProofHP
""")
save(root / "Stage4ThetaEnergyFiniteIntegralUpper.lean", "".join(parts))
print("Exact bound:", total)
print("Decimal preview:", float(total))
PY

mkdir -p stage4_fourth_certificate_build_logs

log="stage4_fourth_certificate_build_logs/energy_integral_base.log"
if ! lake build HodgeProofHP.Stage4ThetaEnergyUpperIntegralBase >"$log" 2>&1; then
  tail -n 100 "$log"
  printf 'STOP: integral base failed; log: %s\n' "$log"
  exit 1
fi
tail -n 15 "$log"

for batch in $(seq 0 39); do
  tag=$(printf '%02d' "$batch")
  log="stage4_fourth_certificate_build_logs/energy_integral_batch_${tag}.log"
  printf '\n[%s] Building integral batch %s/39\n' "$(date +%H:%M:%S)" "$tag"

  if lake build "HodgeProofHP.Stage4ThetaEnergyUpperIntegralBatch${tag}" >"$log" 2>&1; then
    tail -n 12 "$log"
    printf 'PASS: energy integral batch %s\n' "$tag"
  else
    tail -n 100 "$log"
    printf 'STOP: integral batch %s failed; log: %s\n' "$tag" "$log"
    exit 1
  fi
done

log="stage4_fourth_certificate_build_logs/energy_finite_integral_upper.log"
if lake build HodgeProofHP.Stage4ThetaEnergyFiniteIntegralUpper >"$log" 2>&1; then
  tail -n 30 "$log"
  printf '%s\n' 'PASS: Stage4ThetaEnergyFiniteIntegralUpper'
else
  tail -n 100 "$log"
  printf 'STOP: final integral build failed; log: %s\n' "$log"
  exit 1
fi
