#!/usr/bin/env bash
set -euo pipefail

python - <<'PY'
from pathlib import Path
from datetime import datetime
import re

root = Path("HodgeProofHP")
base = root / "Stage4ThetaFourthMomentCertificateBase.lean"
stamp = datetime.now().strftime("%Y%m%d_%H%M%S_%f")
marker = "-- Fourth-moment certificates: two-level rational lookup."

if not base.is_file():
    raise SystemExit(f"STOP: missing {base}")

raw = base.read_bytes()
newline = "\r\n" if b"\r\n" in raw else "\n"
text = raw.decode("utf-8").replace("\r\n", "\n")

if marker in text:
    print(f"ALREADY REPAIRED: {base}")
else:
    values = {}
    pattern = re.compile(
        r"theorem hpThetaFourthCertificate_endpoint_(\d+)\s*:"
        r"\s*(.*?)\s*≤\s*hpThetaTraceEndpointLower",
        re.S
    )

    for b in range(20):
        path = root / f"Stage4ThetaFourthMomentCertificateBatch{b:02d}.lean"
        if not path.is_file():
            raise SystemExit(f"STOP: missing {path}")

        source = path.read_text(encoding="utf-8")
        found = list(pattern.finditer(source))
        expected = list(range(20 * b, 20 * (b + 1)))
        actual = [int(m.group(1)) for m in found]

        if actual != expected:
            raise SystemExit(f"STOP: unexpected endpoint declarations in {path}")

        for m in found:
            i = int(m.group(1))
            value = " ".join(m.group(2).split())
            if not re.fullmatch(r"\([\d\s/]+:\s*ℝ\)", value):
                raise SystemExit(f"STOP: unexpected rational expression at {i}")
            values[i] = value

    if sorted(values) != list(range(400)):
        raise SystemExit("STOP: incomplete rational certificate table")

    definition = re.compile(
        r"(?ms)^def hpThetaFourthCertificateLower\b.*?"
        r"(?=^(?:private\s+)?(?:theorem|lemma|def)\s)"
    )
    matches = list(definition.finditer(text))
    if len(matches) != 1:
        raise SystemExit("STOP: could not isolate the original lower-table definition")

    old = matches[0].group()
    if "max 0" not in old or "match" not in old:
        raise SystemExit("STOP: unexpected original lower-table definition")

    generated = [marker, ""]
    for b in range(20):
        generated.extend([
            "-- Small lookup tables keep numeral simplification manageable.",
            "@[simp]",
            f"def hpThetaFourthCertificateLookup{b:02d} (j : ℕ) : ℝ :=",
            "  match j with"
        ])
        for j in range(20):
            generated.append(f"  | {j} => {values[20 * b + j]}")
        generated.extend(["  | _ => 0", ""])

    generated.extend([
        "def hpThetaFourthCertificateLower (i : ℕ) : ℝ :=",
        "  max 0 (match i / 20 with"
    ])
    for b in range(20):
        generated.append(
            f"    | {b} => hpThetaFourthCertificateLookup{b:02d} (i % 20)"
        )
    generated.extend(["    | _ => 0)", "", ""])

    m = matches[0]
    updated = text[:m.start()] + "\n".join(generated) + text[m.end():]

    backup = Path(str(base) + f".before_lookup_repair_{stamp}")
    backup.write_bytes(raw)
    base.write_bytes(updated.replace("\n", newline).encode("utf-8"))
    print(f"BACKUP: {backup}")
    print(f"REPAIRED: {base}")
    print("PRESERVED: all 400 rational endpoint values")
PY

mkdir -p stage4_fourth_certificate_build_logs

for batch in $(seq -w 0 19); do
    module="HodgeProofHP.Stage4ThetaFourthMomentCertificateBatch${batch}"
    log="stage4_fourth_certificate_build_logs/batch_${batch}.log"

    printf '\n[%s] Building batch %s/19\n' "$(date +%H:%M:%S)" "$batch"

    if lake build "$module" > "$log" 2>&1; then
        tail -n 4 "$log"
        printf 'PASS: batch %s\n' "$batch"
    else
        tail -n 100 "$log"
        printf 'STOP: batch %s failed; log: %s\n' "$batch" "$log"
        exit 1
    fi
done

log="stage4_fourth_certificate_build_logs/final.log"
if lake build HodgeProofHP.Stage4ThetaFourthMomentLowerCertificate > "$log" 2>&1; then
    tail -n 25 "$log"
else
    tail -n 100 "$log"
    printf 'STOP: final certificate failed; log: %s\n' "$log"
    exit 1
fi

printf '%s\n' 'PASS: Stage4ThetaFourthMomentLowerCertificate'
