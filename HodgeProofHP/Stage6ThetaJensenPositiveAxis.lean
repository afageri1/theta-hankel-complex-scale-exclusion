import HodgeProofHP.Stage6ThetaJensenZeroReduction
import HodgeProofHP.Stage4ThetaPhiZeroMomentPositive
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Positive real axis exclusion for the Jensen generating function

Nonnegative coefficients and a positive constant coefficient give F(x).re > 0
for real x >= 0. Hence F has no zeros on that axis, including zero.
The all-real xi zero property is equivalent to all F zeros being strictly
negative real. Neither of these global zero-location properties is proved.
-/

noncomputable section
namespace HodgeProofHP

theorem hpThetaJensenGamma_nonneg (n : ℕ) : 0 ≤ hpThetaJensenGamma n := by
  have hm := hpThetaPhi_evenMoment_nonneg n
  unfold hpThetaJensenGamma
  positivity

theorem hpThetaJensenGamma_zero_pos : 0 < hpThetaJensenGamma 0 := by
  rw [hpThetaJensenGamma_zero]
  simpa [hpThetaPhiEvenMoment, hpThetaPhiMomentZero] using
    hpThetaTrace_phiMomentZero_pos

theorem hpThetaJensen_real_series_term (n : ℕ) (x : ℝ) :
    (hpThetaJensenGamma n : ℂ) * (x : ℂ) ^ n / (Nat.factorial n : ℂ) =
      ((hpThetaJensenGamma n * x ^ n / (Nat.factorial n : ℝ) : ℝ) : ℂ) := by
  push_cast <;> rfl

theorem hpThetaJensenGeneratingFunction_real_hasSum (x : ℝ) :
    HasSum (fun n : ℕ => hpThetaJensenGamma n * x ^ n / (Nat.factorial n : ℝ))
      (hpThetaJensenGeneratingFunction (x : ℂ)).re := by
  have h := Complex.hasSum_re (hpThetaJensenGeneratingFunction_hasSum (x : ℂ))
  simpa only [hpThetaJensen_real_series_term, Complex.ofReal_re] using h

theorem hpThetaJensenGeneratingFunction_real_im_zero (x : ℝ) :
    (hpThetaJensenGeneratingFunction (x : ℂ)).im = 0 := by
  have h : HasSum (fun _ : ℕ => (0 : ℝ))
      (hpThetaJensenGeneratingFunction (x : ℂ)).im := by
    simpa only [hpThetaJensen_real_series_term, Complex.ofReal_im] using
      Complex.hasSum_im (hpThetaJensenGeneratingFunction_hasSum (x : ℂ))
  exact h.unique hasSum_zero

theorem hpThetaJensenGeneratingFunction_real_re_pos (x : ℝ) (hx : 0 ≤ x) :
    0 < (hpThetaJensenGeneratingFunction (x : ℂ)).re := by
  have hnonneg (n : ℕ) :
      0 ≤ hpThetaJensenGamma n * x ^ n / (Nat.factorial n : ℝ) := by
    exact div_nonneg (mul_nonneg (hpThetaJensenGamma_nonneg n) (pow_nonneg hx n))
      (Nat.cast_nonneg _)
  have hle := le_hasSum (hpThetaJensenGeneratingFunction_real_hasSum x) 0
    (fun n _ => hnonneg n)
  have hbound : hpThetaJensenGamma 0 ≤
      (hpThetaJensenGeneratingFunction (x : ℂ)).re := by
    simpa using hle
  exact lt_of_lt_of_le hpThetaJensenGamma_zero_pos hbound

theorem hpThetaJensenGeneratingFunction_real_ne_zero (x : ℝ) (hx : 0 ≤ x) :
    hpThetaJensenGeneratingFunction (x : ℂ) ≠ 0 := by
  intro hzero
  have hpos := hpThetaJensenGeneratingFunction_real_re_pos x hx
  rw [hzero] at hpos
  simpa using hpos

def hpThetaJensenNegativeRealZeros : Prop :=
  ∀ w : ℂ, hpThetaJensenGeneratingFunction w = 0 → w.im = 0 ∧ w.re < 0

theorem hpThetaJensen_negativeRealZeros_iff_nonpositive :
    hpThetaJensenNegativeRealZeros ↔ hpThetaJensenNonpositiveRealZeros := by
  constructor
  · intro h w hw
    obtain ⟨him, hre⟩ := h w hw
    exact ⟨him, hre.le⟩
  · intro h w hw
    obtain ⟨him, hre⟩ := h w hw
    refine ⟨him, ?_⟩
    by_contra hnot
    have hr : w.re = 0 := le_antisymm hre (le_of_not_gt hnot)
    have hwzero : w = 0 := Complex.ext hr him
    rw [hwzero] at hw
    exact hpThetaJensenGeneratingFunction_real_ne_zero 0 (by norm_num) (by simpa using hw)

theorem hpThetaJensen_negativeRealZeros_iff_xiRealZeros :
    hpThetaJensenNegativeRealZeros ↔ hpThetaXiCriticalRealZeros :=
  hpThetaJensen_negativeRealZeros_iff_nonpositive.trans
    hpThetaJensen_zeroLocation_iff_xiRealZeros

#print axioms hpThetaJensenGamma_nonneg
#print axioms hpThetaJensenGamma_zero_pos
#print axioms hpThetaJensen_real_series_term
#print axioms hpThetaJensenGeneratingFunction_real_hasSum
#print axioms hpThetaJensenGeneratingFunction_real_im_zero
#print axioms hpThetaJensenGeneratingFunction_real_re_pos
#print axioms hpThetaJensenGeneratingFunction_real_ne_zero
#print axioms hpThetaJensen_negativeRealZeros_iff_nonpositive
#print axioms hpThetaJensen_negativeRealZeros_iff_xiRealZeros

end HodgeProofHP
