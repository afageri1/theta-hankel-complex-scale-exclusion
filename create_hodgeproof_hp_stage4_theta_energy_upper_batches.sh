#!/usr/bin/env bash
set -euo pipefail

python - <<'PY'
from pathlib import Path
from fractions import Fraction as F
from math import factorial
from datetime import datetime
import csv

root = Path("HodgeProofHP")
stamp = datetime.now().strftime("%Y%m%d_%H%M%S_%f")

def save(path, text):
    if path.exists():
        old = path.read_bytes()
        if old == text.encode("utf-8"):
            print(f"UNCHANGED: {path}")
            return
        backup = path.with_name(path.name + ".before_update_" + stamp)
        backup.write_bytes(old)
        print(f"BACKUP: {backup}")
    path.write_text(text, encoding="utf-8")
    print(f"CREATED: {path}")

def lower(x):
    return sum((x**k / factorial(k) for k in range(12)), F(0))

def upper(x):
    assert 0 <= x <= 1
    return lower(x) + x**12 * 13 / (factorial(12) * 12)

def floor_grid(x, d):
    return F((x.numerator * d) // x.denominator, d)

def ceil_grid(x, d):
    return F(-((-x.numerator * d) // x.denominator), d)

def lean(x):
    return f"({x.numerator} / {x.denominator} : ℝ)"

C = F(12183, 12151)
cells = []
total = F(0)

for i in range(800):
    l, r = F(i, 800), F(i + 1, 800)
    L = floor_grid(lower(2*l), 10**6)
    s = ceil_grid(upper(r), 10**6)
    U = s*s
    t = F(157, 50)*L - r/2
    assert 0 <= t/32 <= 1
    v = floor_grid(lower(t/32), 10**8)
    assert v > 0
    W = ceil_grid(1 / v**32, 10**10)
    a = 4*F(63, 20)**2*U**2 - 6*F(157, 50)*L
    H = ceil_grid(C*a*2*W, 10**8)
    assert H >= 0 and W*v**32 >= 1
    assert C*a*2*W <= H
    total += H**2 * (r**2-l**2)/2
    cells.append((l, r, L, s, U, v, W, H))

assert total < F(17, 200)
print("Exact finite upper sum:", total)
print("Decimal preview:", float(total))
print("This sum still needs its Lean integral comparison and tail bound.")

taylor = (
    "hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, "
    "Finset.sum_range_succ, Nat.factorial"
)

for batch in range(40):
    parts = [
        "import HodgeProofHP.Stage4ThetaKernelIntervalUpper\n\n",
        "/-! Explicit rational upper certificates on twenty intervals. -/\n\n",
        "noncomputable section\n\n",
        "namespace HodgeProofHP\n\n",
    ]
    for i in range(20*batch, 20*batch+20):
        l, r, L, s, U, v, W, H = cells[i]
        parts.append(f"""\
-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_{i} :
    ∀ u : ℝ, {lean(l)} ≤ u → u ≤ {lean(r)} →
      hpRiemannThetaDifferentialKernel u ≤ {lean(H)} := by
  apply hpThetaKernel_rational_interval_upper_certificate
    {lean(l)} {lean(r)} {lean(L)} {lean(U)}
    {lean(v)} {lean(W)} {lean(H)}
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * {lean(l)}) {lean(L)} 12
      (by norm_num)
      (by norm_num [{taylor}])
  · have h := hpThetaTrace_exp_upper_of_taylor
      {lean(r)} {lean(s)} 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [{taylor}])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos {lean(r)})) h 2
    have he :
        (Real.exp {lean(r)}) ^ 2 =
          Real.exp (2 * {lean(r)}) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * {lean(L)} - {lean(r)} / 2) / 32)
      {lean(v)} 12
      (by norm_num)
      (by norm_num [{taylor}])
  · norm_num
  · norm_num

""")
    parts.append(
        f"#print axioms hpThetaEnergyUpper_interval_{20*batch}\n"
        f"#print axioms hpThetaEnergyUpper_interval_{20*batch+19}\n\n"
        "end HodgeProofHP\n"
    )
    save(
        root / f"Stage4ThetaEnergyUpperCertificateBatch{batch:02d}.lean",
        "".join(parts),
    )

imports = "".join(
    f"import HodgeProofHP.Stage4ThetaEnergyUpperCertificateBatch{b:02d}\n"
    for b in range(40)
)
save(
    root / "Stage4ThetaEnergyUpperCertificates.lean",
    imports +
    "\n/-! All eight hundred interval upper certificates. -/\n\n"
    "#print axioms HodgeProofHP.hpThetaEnergyUpper_interval_0\n"
    "#print axioms HodgeProofHP.hpThetaEnergyUpper_interval_799\n"
)

table = Path("stage4_theta_energy_upper_cells.csv")
if table.exists():
    backup = table.with_name(table.name + ".before_update_" + stamp)
    backup.write_bytes(table.read_bytes())
with table.open("w", encoding="utf-8", newline="") as f:
    writer = csv.writer(f)
    writer.writerow(["i", "l", "r", "L", "sqrt_U", "U", "v", "W", "H"])
    for i, cell in enumerate(cells):
        writer.writerow([i, *(str(x) for x in cell)])
print(f"CREATED: {table}")
PY

mkdir -p stage4_fourth_certificate_build_logs

for batch in $(seq 0 39); do
  tag=$(printf '%02d' "$batch")
  module="HodgeProofHP.Stage4ThetaEnergyUpperCertificateBatch${tag}"
  log="stage4_fourth_certificate_build_logs/energy_upper_batch_${tag}.log"

  printf '\n[%s] Building energy upper batch %s/39\n' \
    "$(date +%H:%M:%S)" "$tag"

  if lake build "$module" >"$log" 2>&1; then
    tail -n 12 "$log"
    printf 'PASS: energy upper batch %s\n' "$tag"
  else
    tail -n 100 "$log"
    printf 'STOP: batch %s failed; log: %s\n' "$tag" "$log"
    exit 1
  fi
done

log="stage4_fourth_certificate_build_logs/energy_upper_certificates.log"
if lake build HodgeProofHP.Stage4ThetaEnergyUpperCertificates >"$log" 2>&1; then
  tail -n 20 "$log"
  printf '%s\n' 'PASS: Stage4ThetaEnergyUpperCertificates'
else
  tail -n 100 "$log"
  printf 'STOP: final import build failed; log: %s\n' "$log"
  exit 1
fi
