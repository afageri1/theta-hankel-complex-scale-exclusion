#!/usr/bin/env python3
"""Fail closed on missing, malformed, or unexpected Lean axiom reports."""
import argparse
from pathlib import Path
import re

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
REPORT = re.compile(r"'([^'\r\n]+)' depends on axioms:\s*\[([^\]]*)\]", re.S)

def validate(text, expected=()):
    reports = REPORT.findall(text)
    markers = text.count("depends on axioms")
    if not reports:
        raise ValueError("no axiom report")
    if markers != len(reports):
        raise ValueError("malformed or incomplete axiom report")
    names = set()
    for name, body in reports:
        names.add(name)
        axioms = {item.strip() for item in body.split(",")} if body.strip() else set()
        unexpected = axioms - ALLOWED
        if unexpected:
            raise ValueError(f"unexpected axiom in {name}: {', '.join(sorted(unexpected))}")
    missing = set(expected) - names
    if missing:
        raise ValueError("missing final theorem reports: " + ", ".join(sorted(missing)))
    return len(reports)

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("log", type=Path)
    parser.add_argument("--expect", action="append", default=[])
    args = parser.parse_args()
    try:
        count = validate(args.log.read_text(encoding="utf-8"), args.expect)
    except (OSError, UnicodeError, ValueError) as error:
        parser.exit(1, f"FAIL: {error}\n")
    print(f"PASS: {count} complete axiom reports; all dependencies allowed")

if __name__ == "__main__":
    main()
