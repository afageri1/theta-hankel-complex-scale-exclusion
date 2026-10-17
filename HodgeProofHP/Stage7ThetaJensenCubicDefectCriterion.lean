/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenCubicHigherTuranRoots

/-!
# A quantitative sufficient condition for the cubic higher Turan gap

Write u_n = 1 - gamma(n) gamma(n+2) / gamma(n+1)^2.
The general strict Turan theorem gives 0 < u_n < 1.

The higher gap, divided by (gamma(n+1) gamma(n+2))^2, is
4 u_n u_(n+1) - (u_n + u_(n+1) - u_n u_(n+1))^2.
It is positive if both defects are at most 1/4 and
(u_n - u_(n+1))^2 <= 9 u_n^2 u_(n+1)^2.
For positive defects, the last condition expresses
|1/u_n - 1/u_(n+1)| <= 3 without division.

These quantitative hypotheses remain explicit. Numerical probes are
exploratory and do not discharge any hypothesis of this module.
-/

noncomputable section
namespace HodgeProofHP

def hpThetaJensenTuranDefect (n : ℕ) : ℝ :=
  hpThetaJensenTuranGap n / hpThetaJensenGamma (n + 1) ^ 2

theorem hpThetaJensenTuranDefect_pos (n : ℕ) :
    0 < hpThetaJensenTuranDefect n := by
  exact div_pos (hpThetaJensenTuranGap_pos n)
    (sq_pos_of_pos (hpThetaJensenGamma_pos_allShifts (n + 1)))

theorem hpThetaJensenTuranDefect_lt_one (n : ℕ) :
    hpThetaJensenTuranDefect n < 1 := by
  unfold hpThetaJensenTuranDefect
  rw [div_lt_one (sq_pos_of_pos (hpThetaJensenGamma_pos_allShifts (n + 1)))]
  unfold hpThetaJensenTuranGap
  have hp := mul_pos (hpThetaJensenGamma_pos_allShifts n)
    (hpThetaJensenGamma_pos_allShifts (n + 2))
  linarith

theorem hpCubicDefectMargin_pos_of_bounds (u v : ℝ)
    (hu : 0 < u) (hv : 0 < v) (huUpper : u ≤ 1 / 4) (hvUpper : v ≤ 1 / 4)
    (hstep : (u - v) ^ 2 ≤ 9 * u ^ 2 * v ^ 2) :
    0 < 4 * u * v - (u + v - u * v) ^ 2 := by
  have h1 := mul_nonneg hu.le (sub_nonneg.mpr hvUpper)
  have h2 := mul_nonneg hv.le (sub_nonneg.mpr huUpper)
  have hp := mul_pos hu hv
  have hi : 0 < u + v - 5 * u * v := by
    nlinarith only [h1, h2, hp]
  have hprod : 0 < 2 * (u * v) * (u + v - 5 * u * v) :=
    mul_pos (mul_pos (by norm_num) hp) hi
  nlinarith only [hprod, hstep]

theorem hpThetaJensenHigherTuranGap_eq_defectMargin (n : ℕ) :
    hpThetaJensenHigherTuranGap n =
      (hpThetaJensenGamma (n + 1) * hpThetaJensenGamma (n + 2)) ^ 2 *
        (4 * hpThetaJensenTuranDefect n * hpThetaJensenTuranDefect (n + 1) -
          (hpThetaJensenTuranDefect n + hpThetaJensenTuranDefect (n + 1) -
            hpThetaJensenTuranDefect n * hpThetaJensenTuranDefect (n + 1)) ^ 2) := by
  have hb := (hpThetaJensenGamma_pos_allShifts (n + 1)).ne'
  have hc := (hpThetaJensenGamma_pos_allShifts (n + 2)).ne'
  unfold hpThetaJensenHigherTuranGap hpThetaJensenTuranDefect
    hpThetaJensenTuranGap hpThetaJensenCrossGap
  simp only [Nat.add_assoc]
  field_simp [hb, hc] <;> ring

theorem hpThetaJensenHigherTuranGap_pos_of_defect_bounds (n : ℕ)
    (hu : hpThetaJensenTuranDefect n ≤ 1 / 4)
    (hv : hpThetaJensenTuranDefect (n + 1) ≤ 1 / 4)
    (hstep : (hpThetaJensenTuranDefect n - hpThetaJensenTuranDefect (n + 1)) ^ 2 ≤
      9 * hpThetaJensenTuranDefect n ^ 2 * hpThetaJensenTuranDefect (n + 1) ^ 2) :
    0 < hpThetaJensenHigherTuranGap n := by
  rw [hpThetaJensenHigherTuranGap_eq_defectMargin]
  exact mul_pos
    (sq_pos_of_pos (mul_pos (hpThetaJensenGamma_pos_allShifts (n + 1))
      (hpThetaJensenGamma_pos_allShifts (n + 2))))
    (hpCubicDefectMargin_pos_of_bounds _ _
      (hpThetaJensenTuranDefect_pos n) (hpThetaJensenTuranDefect_pos (n + 1))
      hu hv hstep)

theorem hpThetaJensenCubic_root_im_zero_of_defect_bounds (n : ℕ)
    (hu : hpThetaJensenTuranDefect n ≤ 1 / 4)
    (hv : hpThetaJensenTuranDefect (n + 1) ≤ 1 / 4)
    (hstep : (hpThetaJensenTuranDefect n - hpThetaJensenTuranDefect (n + 1)) ^ 2 ≤
      9 * hpThetaJensenTuranDefect n ^ 2 * hpThetaJensenTuranDefect (n + 1) ^ 2)
    (z : ℂ) (hz : (hpThetaJensenPolynomial 3 n).eval₂ Complex.ofRealHom z = 0) :
    z.im = 0 :=
  hpThetaJensenCubic_root_im_zero_of_higherGap n
    (hpThetaJensenHigherTuranGap_pos_of_defect_bounds n hu hv hstep) z hz

#print axioms hpThetaJensenTuranDefect_pos
#print axioms hpThetaJensenTuranDefect_lt_one
#print axioms hpCubicDefectMargin_pos_of_bounds
#print axioms hpThetaJensenHigherTuranGap_eq_defectMargin
#print axioms hpThetaJensenHigherTuranGap_pos_of_defect_bounds
#print axioms hpThetaJensenCubic_root_im_zero_of_defect_bounds
end HodgeProofHP
