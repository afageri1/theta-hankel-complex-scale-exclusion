#!/usr/bin/env bash
set -euo pipefail

mathlib_root=".lake/packages/mathlib/Mathlib"
if [ ! -d "$mathlib_root" ]; then
  echo "STOP: mathlib source directory not found: $mathlib_root"
  exit 1
fi

cat > HodgeProofHP/Stage3HermiteDensityApiAudit.lean <<'LEAN'
import HodgeProofHP.Stage3PolynomialGaussianL2Map

/-!
Audit the established polynomial Gaussian interface before proving density.
-/

namespace HodgeProofHP

#check hpPolynomialGaussianL2Map
#check hpPolynomialGaussianL2Map_range_eq_span
#check hpPolynomialGaussianL2Map_hermite
#check hpPolynomialGaussianSchwartz_apply
#check hpPolynomialGaussian_memLp
#check hpSchwartzToL2_injective

#check MeasureTheory.MemLp.toLp
#check MeasureTheory.MemLp.coeFn_toLp
#check SchwartzMap.memLp
#check SchwartzMap.toLp

#print axioms hpPolynomialGaussianL2Map_range_eq_span

end HodgeProofHP
LEAN

lake env lean HodgeProofHP/Stage3HermiteDensityApiAudit.lean
lake build HodgeProofHP.Stage3HermiteDensityApiAudit

echo "=== Hermite and polynomial density results ==="
rg -n -i \
  'hermite|polynomial.{0,100}(dense|density|total)|(dense|density).{0,100}(polynomial|gaussian)' \
  "$mathlib_root/Analysis" \
  "$mathlib_root/MeasureTheory" \
  "$mathlib_root/Probability" |
  head -n 100 || true

echo "=== Orthogonal complement and density criteria ==="
rg -n \
  'orthogonal_eq_bot|topologicalClosure_eq_top|mem_orthogonal|orthogonal_span|dense_iff' \
  "$mathlib_root/Analysis/InnerProductSpace" |
  head -n 100 || true

echo "=== Fourier uniqueness and moment uniqueness ==="
rg -n -i \
  'fourier.{0,100}(injective|eq_zero|unique)|(injective|eq_zero|unique).{0,100}fourier|moment.{0,100}(unique|determ|eq)|eq.{0,100}moment' \
  "$mathlib_root/Analysis" \
  "$mathlib_root/MeasureTheory" \
  "$mathlib_root/Probability" |
  head -n 100 || true

echo "=== Gaussian exponential integrability ==="
rg -n \
  'integrable_exp|integrable.*gaussian|exp.*integrable|integrable.*exp' \
  "$mathlib_root/Analysis/SpecialFunctions/Gaussian" \
  "$mathlib_root/Probability" |
  head -n 80 || true
