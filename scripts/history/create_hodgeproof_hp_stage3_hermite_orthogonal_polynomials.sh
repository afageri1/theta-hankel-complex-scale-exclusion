#!/usr/bin/env bash
set -euo pipefail

cat > HodgeProofHP/Stage3HermiteOrthogonalPolynomials.lean <<'LEAN'
import HodgeProofHP.Stage3PolynomialGaussianL2Map
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
Characterize the Hermite orthogonal complement using polynomial Gaussians.
-/

namespace HodgeProofHP

theorem hpHermiteL2Span_mem_orthogonal_iff_polynomial
    (v : HPSpace) :
    v ∈ hpHermiteL2Span.orthogonal ↔
      ∀ p : Polynomial ℂ,
        inner ℂ (hpPolynomialGaussianL2Map p) v = 0 := by
  rw [Submodule.mem_orthogonal]
  constructor
  · intro h p
    exact h (hpPolynomialGaussianL2Map p)
      (hpPolynomialGaussianL2Map_mem_span p)
  · intro h u hu
    have hurange :
        u ∈ LinearMap.range hpPolynomialGaussianL2Map := by
      rw [hpPolynomialGaussianL2Map_range_eq_span]
      exact hu
    rcases hurange with ⟨p, rfl⟩
    exact h p

theorem hpHermiteL2Span_orthogonal_monomial
    (v : HPSpace) (hv : v ∈ hpHermiteL2Span.orthogonal)
    (n : ℕ) :
    inner ℂ
      (hpPolynomialGaussianL2Map
        ((Polynomial.X : Polynomial ℂ) ^ n)) v = 0 := by
  exact
    (hpHermiteL2Span_mem_orthogonal_iff_polynomial v).mp hv
      ((Polynomial.X : Polynomial ℂ) ^ n)

#check Submodule.orthogonal_eq_bot_iff
#check Submodule.mem_orthogonal
#check Submodule.eq_bot_iff
#check hpPolynomialGaussianL2Map_range_eq_span

#print axioms hpHermiteL2Span_mem_orthogonal_iff_polynomial
#print axioms hpHermiteL2Span_orthogonal_monomial

end HodgeProofHP
LEAN

lake env lean HodgeProofHP/Stage3HermiteOrthogonalPolynomials.lean
lake build HodgeProofHP.Stage3HermiteOrthogonalPolynomials

mathlib_root=".lake/packages/mathlib/Mathlib"

echo "=== Exact orthogonal density criterion ==="
rg -n -A 12 -B 3 \
  '^theorem orthogonal_eq_bot_iff|^lemma orthogonal_eq_bot_iff' \
  "$mathlib_root/Analysis/InnerProductSpace" || true

echo "=== Fourier inversion and uniqueness interfaces ==="
rg -n -A 7 \
  '^(theorem|lemma).*([Ii]njective|inversion|fourierInv_fourier|fourier_fourierInv|fourier.*eq|eq.*fourier)' \
  "$mathlib_root/Analysis/Fourier" |
  head -n 160 || true

echo "=== L2 inner product and product integrability ==="
rg -n -A 7 \
  '^(theorem|lemma).*(inner_def|integrable_mul|integrable_inner|integral_inner)' \
  "$mathlib_root/MeasureTheory/Function" |
  head -n 140 || true
