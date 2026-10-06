#!/usr/bin/env bash
set -euo pipefail

python - <<'PY'
from pathlib import Path
from datetime import datetime
import shutil

root = Path("HodgeProofHP")
for name in [
    "Stage4ThetaRealScaledObstruction.lean",
    "Stage4ThetaHankelSpectralScalingNecessary.lean",
]:
    if not (root / name).is_file():
        raise SystemExit(f"STOP: missing {root / name}")

p = root / "Stage4ThetaComplexScaledObstruction.lean"
if p.exists():
    backup = p.with_name(
        p.name + ".before_update_" +
        datetime.now().strftime("%Y%m%d_%H%M%S_%f")
    )
    shutil.copy2(p, backup)
    print(f"BACKUP: {backup}")

source = r'''import HodgeProofHP.Stage4ThetaRealScaledObstruction
import Mathlib.Tactic

/-!
Extend the certified obstruction to arbitrary complex scales.
The second derivative forces any matching scale to be real.
-/

noncomputable section

open MeasureTheory

namespace HodgeProofHP

def hpThetaHankelComplexScaledSpectralProduct
    (c z : ℂ) : ℂ :=
  hpThetaHankelSpectralProduct (c * z)

theorem hpThetaHankelComplexScaledSpectralProduct_ofReal
    (c : ℝ) :
    hpThetaHankelComplexScaledSpectralProduct (c : ℂ) =
      hpThetaHankelScaledSpectralProduct c := by
  rfl

theorem hpThetaHankelComplexScaledSpectralProduct_secondDeriv_zero
    (c : ℂ) :
    deriv (deriv (hpThetaHankelComplexScaledSpectralProduct c)) 0 =
      (-2 : ℂ) * c ^ 2 * (hpThetaFirstTraceEnergy : ℂ) := by
  unfold hpThetaHankelComplexScaledSpectralProduct
  rw [hpTheta_secondDeriv_comp_scale_zero
    hpThetaHankelSpectralProduct
    hpThetaHankelSpectralProduct_differentiable
    hpThetaHankelSpectralProduct_deriv_differentiable,
    hpThetaHankelSpectralProduct_secondDeriv_zero]
  ring

private theorem hpThetaComplexObstruction_momentTwo_nonneg :
    0 ≤ hpThetaPhiMomentTwo := by
  unfold hpThetaPhiMomentTwo
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  exact mul_nonneg (sq_nonneg u)
    (le_of_lt (hpThetaPhi_pos_on_nonnegative u (le_of_lt hu)))

theorem hpThetaHankelComplexScaledSpectralProduct_match_square_identity
    (c : ℂ)
    (hmatch :
      hpThetaHankelComplexScaledSpectralProduct c = hpThetaNormalizedXi) :
    c ^ 2 *
        ((2 * hpThetaFirstTraceEnergy * hpThetaPhiMomentZero : ℝ) : ℂ) =
      (hpThetaPhiMomentTwo : ℂ) := by
  have h0 : 0 < hpThetaPhiMomentZero := by
    have h := hpThetaPhiMomentZero_gt_twelve_twentyFifths
    linarith
  have h0c : (hpThetaPhiMomentZero : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt h0)
  have h := congrArg
    (fun f : ℂ → ℂ => deriv (deriv f) 0) hmatch
  rw [hpThetaHankelComplexScaledSpectralProduct_secondDeriv_zero,
    hpThetaNormalizedXi_secondDeriv_zero,
    hpRiemannXiCritical_secondDeriv_zero_eq_moment,
    ← hpThetaPhiMomentZero_cast_eq_xi_zero] at h
  have hm := (eq_div_iff h0c).mp h
  push_cast
  linear_combination -hm

private theorem hpThetaComplex_im_zero_of_square
    (c : ℂ) (him : (c ^ 2).im = 0)
    (hre : 0 ≤ (c ^ 2).re) :
    c.im = 0 := by
  simp only [pow_two, Complex.mul_im, Complex.mul_re] at him hre
  have hprod : c.re * c.im = 0 := by
    nlinarith only [him]
  rcases mul_eq_zero.mp hprod with hx | hy
  · nlinarith [sq_nonneg c.im]
  · exact hy

theorem hpThetaHankelComplexScaledSpectralProduct_match_im_zero
    (c : ℂ)
    (hmatch :
      hpThetaHankelComplexScaledSpectralProduct c = hpThetaNormalizedXi) :
    c.im = 0 := by
  let d : ℝ :=
    2 * hpThetaFirstTraceEnergy * hpThetaPhiMomentZero
  have hE : 0 < hpThetaFirstTraceEnergy := by
    have h := hpThetaFirstTraceEnergy_gt_seven_hundredths
    linarith
  have h0 : 0 < hpThetaPhiMomentZero := by
    have h := hpThetaPhiMomentZero_gt_twelve_twentyFifths
    linarith
  have hd : 0 < d := by
    dsimp [d]
    positivity
  have hc : c ^ 2 * (d : ℂ) = (hpThetaPhiMomentTwo : ℂ) :=
    hpThetaHankelComplexScaledSpectralProduct_match_square_identity c hmatch
  have hi := congrArg Complex.im hc
  have hr := congrArg Complex.re hc
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, zero_add] at hi
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero] at hr
  have hsIm : (c ^ 2).im = 0 :=
    (mul_eq_zero.mp hi).resolve_right (ne_of_gt hd)
  have hsRe : 0 ≤ (c ^ 2).re := by
    by_contra hneg
    have hbad := mul_neg_of_neg_of_pos (lt_of_not_ge hneg) hd
    rw [hr] at hbad
    have hn := hpThetaComplexObstruction_momentTwo_nonneg
    linarith
  exact hpThetaComplex_im_zero_of_square c hsIm hsRe

theorem hpThetaHankelComplexScaledSpectralProduct_ne_normalizedXi
    (c : ℂ) :
    hpThetaHankelComplexScaledSpectralProduct c ≠ hpThetaNormalizedXi := by
  intro hmatch
  have him :=
    hpThetaHankelComplexScaledSpectralProduct_match_im_zero c hmatch
  have hc : c = (c.re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using him
  have hreal :
      hpThetaHankelScaledSpectralProduct c.re = hpThetaNormalizedXi := by
    rw [hc,
      hpThetaHankelComplexScaledSpectralProduct_ofReal] at hmatch
    exact hmatch
  exact hpThetaHankelScaledSpectralProduct_ne_normalizedXi_certified c.re hreal

theorem hpThetaHankel_no_complex_scale_normalizedXi :
    ¬ ∃ c : ℂ,
      hpThetaHankelComplexScaledSpectralProduct c = hpThetaNormalizedXi := by
  rintro ⟨c, hc⟩
  exact hpThetaHankelComplexScaledSpectralProduct_ne_normalizedXi c hc

theorem hpThetaHankel_no_complex_scale_normalizedXi_explicit :
    ¬ ∃ c : ℂ,
      (fun z : ℂ => hpThetaHankelSpectralProduct (c * z)) =
        hpThetaNormalizedXi := by
  exact hpThetaHankel_no_complex_scale_normalizedXi

#print axioms hpThetaHankelComplexScaledSpectralProduct_secondDeriv_zero
#print axioms hpThetaHankelComplexScaledSpectralProduct_match_square_identity
#print axioms hpThetaHankelComplexScaledSpectralProduct_match_im_zero
#print axioms hpThetaHankelComplexScaledSpectralProduct_ne_normalizedXi
#print axioms hpThetaHankel_no_complex_scale_normalizedXi
#print axioms hpThetaHankel_no_complex_scale_normalizedXi_explicit

end HodgeProofHP
'''
p.write_text(source, encoding="utf-8")
print(f"CREATED: {p}")
PY

mkdir -p stage4_fourth_certificate_build_logs
log="stage4_fourth_certificate_build_logs/complex_scaled_obstruction.log"

if lake build HodgeProofHP.Stage4ThetaComplexScaledObstruction >"$log" 2>&1; then
    tail -n 85 "$log"
    if rg -n 'sorryAx' "$log"; then
        echo "STOP: sorryAx found in build output"
        exit 1
    fi
    echo "PASS: Stage4ThetaComplexScaledObstruction"
else
    tail -n 120 "$log"
    echo "STOP: build failed; log: $log"
    exit 1
fi
