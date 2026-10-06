#!/usr/bin/env bash
set -euo pipefail

for file in \
  HodgeProofHP/Stage3GaussianSchwartzEigen.lean \
  create_hodgeproof_hp_stage3_gaussian_schwartz_eigen.sh
do
  sed -i '/rw \[hpGaussianGroundL2_eq_schwartz\]/{n;/^[[:space:]]*rfl$/d;}' "$file"
done

lake env lean HodgeProofHP/Stage3GaussianSchwartzEigen.lean
lake build HodgeProofHP.Stage3GaussianSchwartzEigen
