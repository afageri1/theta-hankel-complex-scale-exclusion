#!/usr/bin/env bash
set -euo pipefail

lake build HodgeProofHP.Stage4ThetaHankelAdjointSquarePairing

target="HodgeProofHP/Stage4ThetaHankelParseval.lean"

if [ -f "$target" ]; then
  cp -p "$target" "$target.before_update_$(date +%Y%m%d_%H%M%S)"
fi

cat > "$target" <<'LEAN'
import HodgeProofHP.Stage4ThetaHankelAdjointSquarePairing
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
Parseval identities on the theta Hankel space.
The coefficient products are retained in complex form.
No operator trace or determinant identity is asserted here.
-/

namespace HodgeProofHP

theorem hpThetaHankel_parseval_hasSum
    {ι : Type*}
    (b : HilbertBasis ι ℂ HPThetaHankelSpace)
    (f : HPThetaHankelSpace) :
    HasSum
      (fun i => inner ℂ f (b i) * inner ℂ (b i) f)
      ((‖f‖ ^ 2 : ℝ) : ℂ) := by
  have h := b.hasSum_inner_mul_inner f f
  rw [inner_self_eq_norm_sq_to_K] at h
  convert! h using 1 <;>
    simp only [Complex.ofReal_pow] <;> rfl

theorem hpThetaHankel_parseval_summable
    {ι : Type*}
    (b : HilbertBasis ι ℂ HPThetaHankelSpace)
    (f : HPThetaHankelSpace) :
    Summable
      (fun i => inner ℂ f (b i) * inner ℂ (b i) f) :=
  (hpThetaHankel_parseval_hasSum b f).summable

theorem hpThetaHankel_parseval_tsum
    {ι : Type*}
    (b : HilbertBasis ι ℂ HPThetaHankelSpace)
    (f : HPThetaHankelSpace) :
    (∑' i, inner ℂ f (b i) * inner ℂ (b i) f) =
      ((‖f‖ ^ 2 : ℝ) : ℂ) :=
  (hpThetaHankel_parseval_hasSum b f).tsum_eq

theorem hpThetaHankelRow_parseval_hasSum
    {ι : Type*}
    (b : HilbertBasis ι ℂ HPThetaHankelSpace)
    (x : ℝ)
    (hx : MeasureTheory.MemLp
      (fun y => hpThetaHankelKernel x y)
      2 hpThetaHankelMeasure) :
    HasSum
      (fun i =>
        inner ℂ (hpThetaHankelRowL2 x hx) (b i) *
          inner ℂ (b i) (hpThetaHankelRowL2 x hx))
      ((‖hpThetaHankelRowL2 x hx‖ ^ 2 : ℝ) : ℂ) :=
  hpThetaHankel_parseval_hasSum b (hpThetaHankelRowL2 x hx)

theorem hpThetaHankelRow_parseval_tsum
    {ι : Type*}
    (b : HilbertBasis ι ℂ HPThetaHankelSpace)
    (x : ℝ)
    (hx : MeasureTheory.MemLp
      (fun y => hpThetaHankelKernel x y)
      2 hpThetaHankelMeasure) :
    (∑' i,
      inner ℂ (hpThetaHankelRowL2 x hx) (b i) *
        inner ℂ (b i) (hpThetaHankelRowL2 x hx)) =
      ((‖hpThetaHankelRowL2 x hx‖ ^ 2 : ℝ) : ℂ) :=
  (hpThetaHankelRow_parseval_hasSum b x hx).tsum_eq

#print axioms hpThetaHankel_parseval_hasSum
#print axioms hpThetaHankel_parseval_summable
#print axioms hpThetaHankel_parseval_tsum
#print axioms hpThetaHankelRow_parseval_hasSum
#print axioms hpThetaHankelRow_parseval_tsum

end HodgeProofHP
LEAN

lake env lean "$target"
lake build HodgeProofHP.Stage4ThetaHankelParseval

printf '%s\n' 'PASS: Stage4ThetaHankelParseval'
