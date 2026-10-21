/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenDensityBivariateMoments
import HodgeProofHP.Stage7ThetaJensenTuranMomentEquivalence
import HodgeProofHP.Stage7ThetaJensenCubicHigherTuranRoots

/-!
# Exact mixed-moment bridge to the shifted Jensen cubic

At p = n + 1/2 the actual Jensen higher Turan gap equals a strictly
positive normalization times the weighted mixed-moment determinant.
Its positivity is retained as an explicit hypothesis in every root theorem.
This module does not establish that positivity or all-shift cubic hyperbolicity.
-/

noncomputable section
namespace HodgeProofHP

def hpThetaDensityJensenExponent (n : ℕ) : ℝ := (n : ℝ) + 1 / 2

def hpThetaDensityWeightedMixedGap (p : ℝ) : ℝ :=
  (p + 2) * hpThetaDensityMixedMoment p p *
      hpThetaDensityMixedMoment (p + 1) (p + 1) -
    (p + 1) * hpThetaDensityMixedMoment (p + 1) p ^ 2

def hpThetaDensityCubicBridgeScale (n : ℕ) : ℝ :=
  (hpThetaJensenMomentScale n / 2) ^ 4 /
    (4096 * hpThetaDensityJensenExponent n ^ 4 *
      (hpThetaDensityJensenExponent n + 1) ^ 3 *
      (hpThetaDensityJensenExponent n + 2) ^ 2)

theorem hpThetaDensityJensenExponent_pos (n : ℕ) :
    0 < hpThetaDensityJensenExponent n := by
  unfold hpThetaDensityJensenExponent
  positivity

theorem hpThetaDensityCubicBridgeScale_pos (n : ℕ) :
    0 < hpThetaDensityCubicBridgeScale n := by
  have hp := hpThetaDensityJensenExponent_pos n
  have hs := hpThetaJensenMomentScale_pos n
  unfold hpThetaDensityCubicBridgeScale
  positivity

private theorem hpDensityBridge_scale_succ (n : ℕ) :
    hpThetaJensenMomentScale (n + 1) =
      hpThetaJensenMomentScale n / (2 * (2 * (n : ℝ) + 1)) := by
  have hf : (Nat.factorial (2 * n) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (2 * n)
  have ha : 2 * (n : ℝ) + 1 ≠ 0 := by positivity
  have hi : 2 * (n + 1) = (2 * n + 1) + 1 := by omega
  unfold hpThetaJensenMomentScale
  rw [hi]
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field_simp
  <;> first | ring | positivity

private theorem hpDensityBridge_gamma (n : ℕ) :
    hpThetaJensenGamma n = hpThetaJensenMomentScale n / 2 *
      hpThetaDensityRealMoment ((n : ℝ) - 1 / 2) := by
  rw [hpThetaJensenGamma_eq_densityRealMoment]
  unfold hpThetaJensenMomentScale
  ring

theorem hpThetaJensenGamma_density_four (n : ℕ) :
    let p := hpThetaDensityJensenExponent n
    let c := hpThetaJensenMomentScale n / 2
    hpThetaJensenGamma n = c * hpThetaDensityRealMoment (p - 1) ∧
    hpThetaJensenGamma (n + 1) = c * hpThetaDensityRealMoment p / (4 * p) ∧
    hpThetaJensenGamma (n + 2) =
      c * hpThetaDensityRealMoment (p + 1) / (16 * p * (p + 1)) ∧
    hpThetaJensenGamma (n + 3) = c * hpThetaDensityRealMoment (p + 2) /
      (64 * p * (p + 1) * (p + 2)) := by
  dsimp only
  have e0 : (n : ℝ) - 1 / 2 = hpThetaDensityJensenExponent n - 1 := by
    unfold hpThetaDensityJensenExponent
    ring
  have e1 : ((n + 1 : ℕ) : ℝ) - 1 / 2 = hpThetaDensityJensenExponent n := by
    push_cast
    unfold hpThetaDensityJensenExponent
    ring
  have e2 : ((n + 2 : ℕ) : ℝ) - 1 / 2 = hpThetaDensityJensenExponent n + 1 := by
    push_cast
    unfold hpThetaDensityJensenExponent
    ring
  have e3 : ((n + 3 : ℕ) : ℝ) - 1 / 2 = hpThetaDensityJensenExponent n + 2 := by
    push_cast
    unfold hpThetaDensityJensenExponent
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hpDensityBridge_gamma, e0]
  · rw [hpDensityBridge_gamma, e1, hpDensityBridge_scale_succ]
    unfold hpThetaDensityJensenExponent
    field_simp
    <;> first | ring | positivity
  · rw [hpDensityBridge_gamma, e2]
    simp only [show n + 2 = (n + 1) + 1 by omega, hpDensityBridge_scale_succ,
      Nat.cast_add, Nat.cast_one]
    unfold hpThetaDensityJensenExponent
    field_simp
    <;> first | ring | positivity
  · rw [hpDensityBridge_gamma, e3]
    simp only [show n + 3 = (n + 2) + 1 by omega,
      show n + 2 = (n + 1) + 1 by omega, hpDensityBridge_scale_succ,
      Nat.cast_add, Nat.cast_one]
    unfold hpThetaDensityJensenExponent
    field_simp
    <;> first | ring | positivity

theorem hpDensityCubic_normalization_identity (p c a b d e : ℝ) (hp : 0 < p) :
    let g0 := c * a
    let g1 := c * b / (4 * p)
    let g2 := c * d / (16 * p * (p + 1))
    let g3 := c * e / (64 * p * (p + 1) * (p + 2))
    4 * (g1 ^ 2 - g0 * g2) * (g2 ^ 2 - g1 * g3) - (g1 * g2 - g0 * g3) ^ 2 =
      c ^ 4 / (4096 * p ^ 4 * (p + 1) ^ 3 * (p + 2) ^ 2) *
        (4 * (p + 2) * ((p + 1) * b ^ 2 - p * a * d) *
            ((p + 2) * d ^ 2 - (p + 1) * b * e) -
          (p + 1) * ((p + 2) * b * d - p * a * e) ^ 2) := by
  have hp0 : p ≠ 0 := ne_of_gt hp
  have hp1 : p + 1 ≠ 0 := by linarith
  have hp2 : p + 2 ≠ 0 := by linarith
  dsimp only
  field_simp
  <;> ring

theorem hpThetaJensenHigherTuranGap_eq_weightedMixedGap (n : ℕ) :
    hpThetaJensenHigherTuranGap n = hpThetaDensityCubicBridgeScale n *
      hpThetaDensityWeightedMixedGap (hpThetaDensityJensenExponent n) := by
  rcases hpThetaJensenGamma_density_four n with ⟨h0, h1, h2, h3⟩
  rw [hpThetaDensityWeightedMixedGap,
    hpThetaDensityMixedMoment_higher_gap_eq _ (hpThetaDensityJensenExponent_pos n)]
  unfold hpThetaJensenHigherTuranGap hpThetaJensenTuranGap hpThetaJensenCrossGap
  simp only [Nat.add_assoc]
  rw [h0, h1, h2, h3]
  unfold hpThetaDensityCubicBridgeScale hpThetaDensityMomentTuran
    hpThetaDensityMomentCross
  simp only [show hpThetaDensityJensenExponent n + 1 - 1 =
      hpThetaDensityJensenExponent n by ring,
    show hpThetaDensityJensenExponent n + 1 + 1 =
      hpThetaDensityJensenExponent n + 2 by ring]
  exact hpDensityCubic_normalization_identity _ _ _ _ _ _
    (hpThetaDensityJensenExponent_pos n)

theorem hpThetaJensenHigherTuranGap_pos_iff_weightedMixedGap (n : ℕ) :
    0 < hpThetaJensenHigherTuranGap n ↔
      0 < hpThetaDensityWeightedMixedGap (hpThetaDensityJensenExponent n) := by
  rw [hpThetaJensenHigherTuranGap_eq_weightedMixedGap]
  exact mul_pos_iff_of_pos_left (hpThetaDensityCubicBridgeScale_pos n)

theorem hpThetaJensenCubic_discr_pos_iff_weightedMixedGap (n : ℕ) :
    0 < (hpThetaJensenShiftedCubic n).discr ↔
      0 < hpThetaDensityWeightedMixedGap (hpThetaDensityJensenExponent n) := by
  rw [hpThetaJensenShiftedCubic_discr_eq_higherGap]
  exact (mul_pos_iff_of_pos_left (by norm_num : (0 : ℝ) < 27)).trans
    (hpThetaJensenHigherTuranGap_pos_iff_weightedMixedGap n)

theorem hpThetaJensenCubic_root_im_zero_of_weightedMixedGap (n : ℕ)
    (hgap : 0 < hpThetaDensityWeightedMixedGap (hpThetaDensityJensenExponent n))
    (z : ℂ) (hz : (hpThetaJensenPolynomial 3 n).eval₂ Complex.ofRealHom z = 0) :
    z.im = 0 := by
  exact hpThetaJensenCubic_root_im_zero_of_higherGap n
    ((hpThetaJensenHigherTuranGap_pos_iff_weightedMixedGap n).mpr hgap) z hz

theorem hpThetaJensenCubic_allShifts_realZeros_of_weightedMixedGaps
    (hgap : ∀ n : ℕ,
      0 < hpThetaDensityWeightedMixedGap (hpThetaDensityJensenExponent n)) :
    ∀ (n : ℕ) (z : ℂ),
      (hpThetaJensenPolynomial 3 n).eval₂ Complex.ofRealHom z = 0 → z.im = 0 := by
  intro n z hz
  exact hpThetaJensenCubic_root_im_zero_of_weightedMixedGap n (hgap n) z hz

#print axioms hpThetaDensityJensenExponent_pos
#print axioms hpThetaDensityCubicBridgeScale_pos
#print axioms hpThetaJensenGamma_density_four
#print axioms hpDensityCubic_normalization_identity
#print axioms hpThetaJensenHigherTuranGap_eq_weightedMixedGap
#print axioms hpThetaJensenHigherTuranGap_pos_iff_weightedMixedGap
#print axioms hpThetaJensenCubic_discr_pos_iff_weightedMixedGap
#print axioms hpThetaJensenCubic_root_im_zero_of_weightedMixedGap
#print axioms hpThetaJensenCubic_allShifts_realZeros_of_weightedMixedGaps
end HodgeProofHP
