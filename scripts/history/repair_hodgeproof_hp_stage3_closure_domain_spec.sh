#!/usr/bin/env bash
set -euo pipefail

file=HodgeProofHP/Stage3ClosureDomainSpec.lean

if ! grep -Fq \
  'LinearPMap.domain_mono hpHarmonicCoreOperator_le_closure' "$file"; then
  echo "STOP: expected line not found in $file"
  exit 1
fi

cp "$file" "$file.before_domain_mono_fix"

sed -i \
  's/LinearPMap\.domain_mono hpHarmonicCoreOperator_le_closure/LinearPMap.domain_mono.monotone hpHarmonicCoreOperator_le_closure/' \
  "$file"

lake build HodgeProofHP.Stage3ClosureDomainSpec
