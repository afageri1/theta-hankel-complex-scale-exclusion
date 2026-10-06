#!/usr/bin/env bash
set -euo pipefail

python - <<'PY'
from pathlib import Path
from datetime import datetime
import shutil

root = Path("HodgeProofHP")
required = [
    "Stage4ThetaTriangleRayleighBridge.lean",
    "Stage4ThetaHankelSpectralSquareBounds.lean",
    "Stage4ThetaHankelAdjointSquarePairing.lean",
]
for name in required:
    if not (root / name).is_file():
        raise SystemExit(f"STOP: missing {root / name}")

p = root / "Stage4ThetaHankelQLowerBound.lean"
if p.exists():
    backup = p.with_name(
        p.name + ".before_update_" +
        datetime.now().strftime("%Y%m%d_%H%M%S_%f")
    )
    shutil.copy2(p, backup)
    print(f"BACKUP: {backup}")

source = r'''import HodgeProofHP.Stage4ThetaTriangleRayleighBridge
import HodgeProofHP.Stage4ThetaHankelSpectralSquareBounds
import HodgeProofHP.Stage4ThetaHankelAdjointSquarePairing
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Tactic

/-!
The spectral square energy bounds the fourth power of the action
on a unit vector. The certified triangle test vector then supplies
a strict rational lower bound.
-/

noncomputable section

namespace HodgeProofHP

private theorem hpThetaQ_repr_norm_sq_hasSum
    (f : HPThetaHankelSpace) :
    HasSum
      (fun i : HPThetaHankelSpectralIndex =>
        ‖(hpThetaHankelSpectralBasis.repr f) i‖ ^ 2)
      (‖f‖ ^ 2) := by
  have h :=
    (lp.hasSum_inner (𝕜 := ℂ)
      (hpThetaHankelSpectralBasis.repr f)
      (hpThetaHankelSpectralBasis.repr f)).map
        Complex.reCLM Complex.reCLM.continuous
  change HasSum
    (fun i : HPThetaHankelSpectralIndex =>
      RCLike.re (inner ℂ
        ((hpThetaHankelSpectralBasis.repr f) i)
        ((hpThetaHankelSpectralBasis.repr f) i)))
    (RCLike.re (inner ℂ
      (hpThetaHankelSpectralBasis.repr f)
      (hpThetaHankelSpectralBasis.repr f))) at h
  simpa only [inner_self_eq_norm_sq,
    LinearIsometryEquiv.norm_map] using h

private theorem hpThetaQ_adjointSquare_inner_swap
    (f g : HPThetaHankelSpace) :
    inner ℂ f (hpThetaHankelAdjointSquare g) =
      inner ℂ (hpThetaHankelAdjointSquare f) g := by
  calc
    inner ℂ f (hpThetaHankelAdjointSquare g) =
        inner ℂ (hpThetaHankelOperator f)
          (hpThetaHankelOperator g) := by
      rw [hpThetaHankelAdjointSquare_apply,
        ContinuousLinearMap.adjoint_inner_right]
    _ = inner ℂ (hpThetaHankelAdjointSquare f) g := by
      rw [hpThetaHankelAdjointSquare_apply,
        ContinuousLinearMap.adjoint_inner_left]

theorem hpThetaHankelAdjointSquare_repr_coefficient
    (f : HPThetaHankelSpace)
    (i : HPThetaHankelSpectralIndex) :
    (hpThetaHankelSpectralBasis.repr
      (hpThetaHankelAdjointSquare f)) i =
        (i.1.re : ℂ) *
          (hpThetaHankelSpectralBasis.repr f) i := by
  rw [HilbertBasis.repr_apply_apply,
    HilbertBasis.repr_apply_apply,
    hpThetaQ_adjointSquare_inner_swap,
    hpThetaHankelSpectralBasis_apply,
    hpThetaHankelSpectralValue_eq_cast_re]
  change
    inner ℂ ((i.1.re : ℂ) • hpThetaHankelSpectralBasis i) f =
      (i.1.re : ℂ) * inner ℂ (hpThetaHankelSpectralBasis i) f
  rw [inner_smul_left]
  have hc :
      (starRingEnd ℂ) (i.1.re : ℂ) = (i.1.re : ℂ) := by
    change star (Complex.ofReal i.1.re) = Complex.ofReal i.1.re
    simp
  rw [hc]

private theorem hpThetaQ_repr_coefficient_norm_sq
    (f : HPThetaHankelSpace)
    (i : HPThetaHankelSpectralIndex) :
    ‖(hpThetaHankelSpectralBasis.repr
      (hpThetaHankelAdjointSquare f)) i‖ ^ 2 =
        i.1.re ^ 2 *
          ‖(hpThetaHankelSpectralBasis.repr f) i‖ ^ 2 := by
  rw [hpThetaHankelAdjointSquare_repr_coefficient, norm_mul]
  have hn : ‖(i.1.re : ℂ)‖ = i.1.re := by
    simp [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hpThetaHankelSpectralValue_re_nonneg i)]
  rw [hn]
  ring

theorem hpThetaHankelAdjointSquare_norm_sq_le_square_energy
    (f : HPThetaHankelSpace) :
    ‖hpThetaHankelAdjointSquare f‖ ^ 2 ≤
      hpThetaHankelSpectralSquareEnergy * ‖f‖ ^ 2 := by
  have hs := hpThetaQ_repr_norm_sq_hasSum
    (hpThetaHankelAdjointSquare f)
  have ht := (hpThetaQ_repr_norm_sq_hasSum f).mul_left
    hpThetaHankelSpectralSquareEnergy
  have hpoint (i : HPThetaHankelSpectralIndex) :
      ‖(hpThetaHankelSpectralBasis.repr
        (hpThetaHankelAdjointSquare f)) i‖ ^ 2 ≤
      hpThetaHankelSpectralSquareEnergy *
        ‖(hpThetaHankelSpectralBasis.repr f) i‖ ^ 2 := by
    rw [hpThetaQ_repr_coefficient_norm_sq]
    exact mul_le_mul_of_nonneg_right
      (hpThetaHankelSpectralValue_re_sq_le_square_energy i)
      (sq_nonneg _)
  calc
    ‖hpThetaHankelAdjointSquare f‖ ^ 2 =
        ∑' i : HPThetaHankelSpectralIndex,
          ‖(hpThetaHankelSpectralBasis.repr
            (hpThetaHankelAdjointSquare f)) i‖ ^ 2 :=
      hs.tsum_eq.symm
    _ ≤ ∑' i : HPThetaHankelSpectralIndex,
        hpThetaHankelSpectralSquareEnergy *
          ‖(hpThetaHankelSpectralBasis.repr f) i‖ ^ 2 :=
      Summable.tsum_le_tsum hpoint hs.summable ht.summable
    _ = hpThetaHankelSpectralSquareEnergy * ‖f‖ ^ 2 :=
      ht.tsum_eq

theorem hpThetaHankel_action_fourth_le_square_energy_of_norm_one
    (f : HPThetaHankelSpace) (hf : ‖f‖ = 1) :
    ‖hpThetaHankelOperator f‖ ^ 4 ≤
      hpThetaHankelSpectralSquareEnergy := by
  have hinner :
      ‖hpThetaHankelOperator f‖ ^ 2 ≤
        ‖hpThetaHankelAdjointSquare f‖ := by
    calc
      ‖hpThetaHankelOperator f‖ ^ 2 =
          (inner ℂ f (hpThetaHankelAdjointSquare f)).re :=
        (hpThetaHankelAdjointSquare_inner_re f).symm
      _ ≤ ‖inner ℂ f (hpThetaHankelAdjointSquare f)‖ :=
        Complex.re_le_norm _
      _ ≤ ‖f‖ * ‖hpThetaHankelAdjointSquare f‖ :=
        norm_inner_le_norm _ _
      _ = ‖hpThetaHankelAdjointSquare f‖ := by rw [hf, one_mul]
  have hs :
      ‖hpThetaHankelAdjointSquare f‖ ^ 2 ≤
        hpThetaHankelSpectralSquareEnergy := by
    simpa only [hf, one_pow, mul_one] using
      hpThetaHankelAdjointSquare_norm_sq_le_square_energy f
  have hmul := mul_nonneg
    (sub_nonneg.mpr hinner)
    (add_nonneg
      (norm_nonneg (hpThetaHankelAdjointSquare f))
      (sq_nonneg ‖hpThetaHankelOperator f‖))
  nlinarith only [hmul, hs]

theorem hpThetaHankelSpectralSquareEnergy_ge_triangle_fourth :
    hpThetaHankelTriangleRayleighLower ^ 4 ≤
      hpThetaHankelSpectralSquareEnergy := by
  have hT :
      hpThetaHankelTriangleRayleighLower ≤
        ‖hpThetaHankelOperator hpThetaTriangleTestVector‖ := by
    have h := hpThetaTriangleTestVector_inner_re_le_action_norm
    rw [hpThetaTriangleTestVector_inner_eq_rayleigh,
      Complex.ofReal_re] at h
    exact h
  have hTpos : 0 ≤ hpThetaHankelTriangleRayleighLower := by
    have h := hpThetaHankelTriangleRayleighLower_gt
    linarith
  calc
    hpThetaHankelTriangleRayleighLower ^ 4 ≤
        ‖hpThetaHankelOperator hpThetaTriangleTestVector‖ ^ 4 := by
      gcongr
    _ ≤ hpThetaHankelSpectralSquareEnergy :=
      hpThetaHankel_action_fourth_le_square_energy_of_norm_one
        hpThetaTriangleTestVector hpThetaTriangleTestVector_norm

theorem hpThetaHankelSpectralSquareEnergy_gt_triangle_certificate :
    (117 / 500 : ℝ) ^ 4 <
      hpThetaHankelSpectralSquareEnergy := by
  have hT := hpThetaHankelTriangleRayleighLower_gt
  have hTpos : 0 < hpThetaHankelTriangleRayleighLower := by
    linarith
  have hpow :
      (117 / 500 : ℝ) ^ 4 <
        hpThetaHankelTriangleRayleighLower ^ 4 := by
    gcongr
  exact lt_of_lt_of_le hpow
    hpThetaHankelSpectralSquareEnergy_ge_triangle_fourth

#print axioms hpThetaHankelAdjointSquare_repr_coefficient
#print axioms hpThetaHankelAdjointSquare_norm_sq_le_square_energy
#print axioms hpThetaHankel_action_fourth_le_square_energy_of_norm_one
#print axioms hpThetaHankelSpectralSquareEnergy_ge_triangle_fourth
#print axioms hpThetaHankelSpectralSquareEnergy_gt_triangle_certificate

end HodgeProofHP
'''
p.write_text(source, encoding="utf-8")
print(f"CREATED: {p}")
PY

mkdir -p stage4_fourth_certificate_build_logs
log="stage4_fourth_certificate_build_logs/q_lower_bound.log"

if lake build HodgeProofHP.Stage4ThetaHankelQLowerBound >"$log" 2>&1; then
    tail -n 55 "$log"
    echo "PASS: Stage4ThetaHankelQLowerBound"
else
    tail -n 100 "$log"
    echo "STOP: build failed; log: $log"
    exit 1
fi
