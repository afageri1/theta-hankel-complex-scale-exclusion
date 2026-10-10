#!/usr/bin/env bash
set -euo pipefail

file=HodgeProofHP/Stage3SecondDerivativeAction.lean
backup="$file.before_remove_extra_tactics"

if [[ ! -f "$file" || -e "$backup" ]]; then
  echo "Missing source or backup already exists; stopped." >&2
  exit 1
fi

if ! rg -q '^  funext y$' "$file" ||
   ! rg -q '^  exact SchwartzMap.derivCLM_apply ℂ f y$' "$file"; then
  echo "Expected proof lines not found; stopped." >&2
  exit 1
fi

cp "$file" "$backup"
sed -i '/^  funext y$/,+1d' "$file"

lake build HodgeProofHP.Stage3SecondDerivativeAction
