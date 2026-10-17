/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenCubicDefectCriterion

/-!
# An unconditional upper bound for the actual Turan defects

The integral of t^(2n) (t^2-c)^2 Phi(t) is nonnegative.
Centering at c = M_(n+1)/M_n proves log-convexity of the even
moments. Exact factorial normalization then gives
0 < u_n <= 2/(2n+3), hence u_n <= 1/4 for n >= 3.

For cubic real zeros at shifts n >= 3, only the squared step
hypothesis from the defect criterion remains. It is not proved here.
No unbounded-degree hyperbolicity or RH conclusion is asserted.
-/

noncomputable section
open MeasureTheory
namespace HodgeProofHP

theorem hpThetaPhiEvenMoment_pos_all (n : ℕ) :
    0 < hpThetaPhiEvenMoment n := by
  exact hpThetaCNV_integral_pos_of_pos_on_Ioi _
    (hpThetaPhi_evenMoment_integrableOn n)
    (fun t ht => mul_pos (pow_pos ht _)
      (hpThetaPhi_pos_on_nonnegative t ht.le))

theorem hpThetaPhiEvenMoment_variance_nonneg (n : ℕ) (c : ℝ) :
    0 ≤ hpThetaPhiEvenMoment (n + 2) -
      2 * c * hpThetaPhiEvenMoment (n + 1) + c ^ 2 * hpThetaPhiEvenMoment n := by
  have h0 := hpThetaPhi_evenMoment_integrableOn n
  have h1 := hpThetaPhi_evenMoment_integrableOn (n + 1)
  have h2 := hpThetaPhi_evenMoment_integrableOn (n + 2)
  have hp : 0 ≤ ∫ t : ℝ in Set.Ioi 0,
      (t ^ (2 * (n + 2)) * hpRiemannThetaDifferentialKernel t -
        (2 * c) * (t ^ (2 * (n + 1)) * hpRiemannThetaDifferentialKernel t)) +
        c ^ 2 * (t ^ (2 * n) * hpRiemannThetaDifferentialKernel t) := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change 0 ≤
      (t ^ (2 * (n + 2)) * hpRiemannThetaDifferentialKernel t -
        (2 * c) * (t ^ (2 * (n + 1)) * hpRiemannThetaDifferentialKernel t)) +
        c ^ 2 * (t ^ (2 * n) * hpRiemannThetaDifferentialKernel t)
    have he :
        (t ^ (2 * (n + 2)) * hpRiemannThetaDifferentialKernel t -
          (2 * c) * (t ^ (2 * (n + 1)) * hpRiemannThetaDifferentialKernel t)) +
          c ^ 2 * (t ^ (2 * n) * hpRiemannThetaDifferentialKernel t) =
        t ^ (2 * n) * (t ^ 2 - c) ^ 2 * hpRiemannThetaDifferentialKernel t := by
      have hn1 : 2 * (n + 1) = 2 * n + 2 := by omega
      have hn2 : 2 * (n + 2) = 2 * n + 4 := by omega
      rw [hn1, hn2, pow_add, pow_add]
      ring
    rw [he]
    exact mul_nonneg (mul_nonneg (pow_nonneg ht.le _) (sq_nonneg _))
      (hpThetaPhi_pos_on_nonnegative t ht.le).le
  have hadd := integral_add (h2.sub (h1.const_mul (2 * c))) (h0.const_mul (c ^ 2))
  have hsub := integral_sub h2 (h1.const_mul (2 * c))
  simp only [Pi.sub_apply, Pi.add_apply] at hadd hsub
  rw [hadd, hsub] at hp
  simp only [integral_const_mul] at hp
  exact hp

theorem hpThetaPhiEvenMoment_logConvex (n : ℕ) :
    hpThetaPhiEvenMoment (n + 1) ^ 2 ≤
      hpThetaPhiEvenMoment n * hpThetaPhiEvenMoment (n + 2) := by
  let c : ℝ := hpThetaPhiEvenMoment (n + 1) / hpThetaPhiEvenMoment n
  have h0 := hpThetaPhiEvenMoment_pos_all n
  have hm : c * hpThetaPhiEvenMoment n = hpThetaPhiEvenMoment (n + 1) :=
    div_mul_cancel₀ _ h0.ne'
  have hp := mul_nonneg h0.le (hpThetaPhiEvenMoment_variance_nonneg n c)
  have he : hpThetaPhiEvenMoment n *
      (hpThetaPhiEvenMoment (n + 2) - 2 * c * hpThetaPhiEvenMoment (n + 1) +
        c ^ 2 * hpThetaPhiEvenMoment n) =
      hpThetaPhiEvenMoment n * hpThetaPhiEvenMoment (n + 2) -
        hpThetaPhiEvenMoment (n + 1) ^ 2 := by
    calc
      _ = hpThetaPhiEvenMoment n * hpThetaPhiEvenMoment (n + 2) -
          2 * (c * hpThetaPhiEvenMoment n) * hpThetaPhiEvenMoment (n + 1) +
          (c * hpThetaPhiEvenMoment n) ^ 2 := by ring
      _ = _ := by rw [hm]; ring
  rw [he] at hp
  linarith

theorem hpThetaJensenGamma_weighted_logConvex (n : ℕ) :
    (2 * (n : ℝ) + 1) * hpThetaJensenGamma (n + 1) ^ 2 ≤
      (2 * (n : ℝ) + 3) * hpThetaJensenGamma n * hpThetaJensenGamma (n + 2) := by
  have ha : 2 * (n : ℝ) + 1 ≠ 0 := by positivity
  have hb : 2 * (n : ℝ) + 3 ≠ 0 := by positivity
  have hzero : hpThetaJensenGamma n =
      hpThetaJensenMomentScale n * hpThetaPhiEvenMoment n := by
    unfold hpThetaJensenGamma hpThetaJensenMomentScale
    ring
  have he :
      (2 * (n : ℝ) + 3) * hpThetaJensenGamma n * hpThetaJensenGamma (n + 2) -
        (2 * (n : ℝ) + 1) * hpThetaJensenGamma (n + 1) ^ 2 =
      hpThetaJensenMomentScale n ^ 2 / (4 * (2 * (n : ℝ) + 1)) *
        (hpThetaPhiEvenMoment n * hpThetaPhiEvenMoment (n + 2) -
          hpThetaPhiEvenMoment (n + 1) ^ 2) := by
    rw [hpThetaJensenGamma_succ_momentScale,
      hpThetaJensenGamma_add_two_momentScale, hzero]
    field_simp [ha, hb]
    ring
  have hp : 0 ≤
      hpThetaJensenMomentScale n ^ 2 / (4 * (2 * (n : ℝ) + 1)) *
        (hpThetaPhiEvenMoment n * hpThetaPhiEvenMoment (n + 2) -
          hpThetaPhiEvenMoment (n + 1) ^ 2) :=
    mul_nonneg (by positivity) (sub_nonneg.mpr (hpThetaPhiEvenMoment_logConvex n))
  rw [← he] at hp
  linarith

theorem hpThetaJensenTuranDefect_le_reciprocal (n : ℕ) :
    hpThetaJensenTuranDefect n ≤ 2 / (2 * (n : ℝ) + 3) := by
  apply (le_div_iff₀ (by positivity : 0 < 2 * (n : ℝ) + 3)).mpr
  unfold hpThetaJensenTuranDefect
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀
    (sq_pos_of_pos (hpThetaJensenGamma_pos_allShifts (n + 1)))).mpr
  unfold hpThetaJensenTuranGap
  have h := hpThetaJensenGamma_weighted_logConvex n
  nlinarith only [h]

theorem hpThetaJensenTuranDefect_le_quarter_of_three_le (n : ℕ) (hn : 3 ≤ n) :
    hpThetaJensenTuranDefect n ≤ 1 / 4 := by
  have hn' : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  calc
    hpThetaJensenTuranDefect n ≤ 2 / (2 * (n : ℝ) + 3) :=
      hpThetaJensenTuranDefect_le_reciprocal n
    _ ≤ 1 / 4 := by
      apply (div_le_iff₀ (by positivity : 0 < 2 * (n : ℝ) + 3)).mpr
      linarith

theorem hpThetaJensenCubic_root_im_zero_of_step_bound
    (n : ℕ) (hn : 3 ≤ n)
    (hstep : (hpThetaJensenTuranDefect n - hpThetaJensenTuranDefect (n + 1)) ^ 2 ≤
      9 * hpThetaJensenTuranDefect n ^ 2 * hpThetaJensenTuranDefect (n + 1) ^ 2)
    (z : ℂ) (hz : (hpThetaJensenPolynomial 3 n).eval₂ Complex.ofRealHom z = 0) :
    z.im = 0 :=
  hpThetaJensenCubic_root_im_zero_of_defect_bounds n
    (hpThetaJensenTuranDefect_le_quarter_of_three_le n hn)
    (hpThetaJensenTuranDefect_le_quarter_of_three_le (n + 1) (by omega))
    hstep z hz

#print axioms hpThetaPhiEvenMoment_pos_all
#print axioms hpThetaPhiEvenMoment_variance_nonneg
#print axioms hpThetaPhiEvenMoment_logConvex
#print axioms hpThetaJensenGamma_weighted_logConvex
#print axioms hpThetaJensenTuranDefect_le_reciprocal
#print axioms hpThetaJensenTuranDefect_le_quarter_of_three_le
#print axioms hpThetaJensenCubic_root_im_zero_of_step_bound
end HodgeProofHP
