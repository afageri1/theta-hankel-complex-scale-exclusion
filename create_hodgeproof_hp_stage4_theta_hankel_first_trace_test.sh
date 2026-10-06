#!/usr/bin/env bash
set -euo pipefail

if [[ ! -f lakefile.lean && ! -f lakefile.toml ]]; then
  echo "STOP: run from ~/hodgeproof-hp"
  exit 1
fi

lake build HodgeProofHP.Stage4ThetaHankelSelfAdjoint

target="HodgeProofHP/Stage4ThetaHankelFirstTraceAudit.lean"

if [[ -f "$target" ]]; then
  cp "$target" \
    "${target}.before_create_$(date +%Y%m%d_%H%M%S)_$$"
fi

cat > "$target" <<'LEAN'
import HodgeProofHP.Stage4ThetaHankelSelfAdjoint

/-!
Definitions used to check the normalization of a numerical
first-trace test. No numerical conclusion is asserted in Lean.
-/

namespace HodgeProofHP

#print hpRiemannThetaKernel
#print hpRiemannThetaLogProfile
#print hpRiemannThetaDifferentialKernel
#print hpRiemannXi
#print hpRiemannXiCritical

end HodgeProofHP
LEAN

lake env lean "$target"

venv_dir=".venv-hp-first-trace"

if [[ ! -d "$venv_dir" ]]; then
  python -m venv "$venv_dir"
fi

if [[ -f "$venv_dir/Scripts/python.exe" ]]; then
  trace_python="$venv_dir/Scripts/python.exe"
else
  trace_python="$venv_dir/bin/python"
fi

"$trace_python" -m pip install "mpmath==1.4.1"

"$trace_python" - <<'PY'
import mpmath as mp

print("\nNUMERICAL FIRST-TRACE TEST")
print("Candidate: det(I - z^2 A* A) = Xi(z)/Xi(0)")
print("Theta convention: theta(t)-1 = 2 sum exp(-pi*n^2*t)")
print("Finite sums and quadrature; no certified error bounds.\n")

runs = []

for dps, terms, endpoint in [(30, 10, 3), (50, 14, 4)]:
    mp.mp.dps = dps

    def phi(u):
        t = mp.exp(2*u)
        return 2*mp.exp(u/2)*mp.fsum(
            (4*a*a - 6*a)*mp.exp(-a)
            for n in range(1, terms + 1)
            for a in [mp.pi*n*n*t]
        )

    cuts = [
        mp.mpf(0), mp.mpf("0.125"), mp.mpf("0.25"),
        mp.mpf("0.5"), mp.mpf(1), mp.mpf(2),
        mp.mpf(3)
    ]
    if endpoint > 3:
        cuts.append(mp.mpf(endpoint))

    moment0 = mp.quad(phi, cuts)
    moment2 = mp.quad(lambda u: u*u*phi(u), cuts)
    energy = mp.quad(lambda u: u*phi(u)**2, cuts)

    def xi(z):
        s = mp.mpf("0.5") + 1j*z
        return (
            s*(s-1)*mp.power(mp.pi, -s/2)
            * mp.gamma(s/2)*mp.zeta(s)/2
        )

    xi0 = mp.re(xi(0))
    xi_ratio = mp.re(-mp.diff(xi, 0, 2)/(2*xi(0)))
    moment_ratio = moment2/(2*moment0)

    print(f"dps={dps}, terms={terms}, endpoint={endpoint}")
    for label, value in [
        ("Integral Phi", moment0),
        ("Xi(0), gamma-zeta formula", xi0),
        ("E = integral u*Phi^2", energy),
        ("Moment ratio", moment_ratio),
        ("-Xi''(0)/(2 Xi(0))", xi_ratio),
        ("E minus Xi ratio", energy-xi_ratio),
        ("E / Xi ratio", energy/xi_ratio),
        ("Normalization cross-check", abs(moment0-xi0)),
        ("Derivative cross-check", abs(moment_ratio-xi_ratio)),
    ]:
        print(f"{label}: {mp.nstr(value, 28)}")
    print()
    runs.append((energy, xi_ratio))

mp.mp.dps = 50
print("Change between runs:")
print("E:", mp.nstr(abs(runs[1][0]-runs[0][0]), 8))
print("Xi ratio:", mp.nstr(abs(runs[1][1]-runs[0][1]), 8))
print("\nNumerical evidence of mismatch at the current normalization.")
print("This is not a Lean proof or a certified numerical enclosure.")
PY

echo "DONE: numerical first-trace test"
