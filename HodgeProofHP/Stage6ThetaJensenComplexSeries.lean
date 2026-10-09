import HodgeProofHP.Stage6ThetaPhiComplexCoshConvergence
import HodgeProofHP.Stage4ThetaPhiPositiveLowerBound
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Tactic

/-!
# Absolutely convergent complex xi moment and Jensen series

Extract all moment coefficients from the complex integral expansion.
Use positivity and real partial-sum convergence to prove absolute
summability, and identify the full Jensen-normalized series with xi(i*z).
This module does not assert any general Jensen hyperbolicity criterion.
-/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology
namespace HodgeProofHP

def hpThetaPhiComplexMomentTerm (n : ℕ) (z : ℂ) : ℂ :=
  (z ^ (2 * n) / (Nat.factorial (2 * n) : ℂ)) * (hpThetaPhiEvenMoment n : ℂ)

theorem hpThetaPhi_evenMoment_nonneg (n : ℕ) :
    0 ≤ hpThetaPhiEvenMoment n := by
  unfold hpThetaPhiEvenMoment
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  exact mul_nonneg (pow_nonneg (le_of_lt hu) _)
    (hpThetaPhi_pos_on_nonnegative u (le_of_lt hu)).le

theorem hpThetaPhi_complexCoshPartial_integral_eq_moments (N : ℕ) (z : ℂ) :
    (∫ u : ℝ in Set.Ioi 0,
      hpThetaPhiComplexCoshPartial N (z * (u : ℂ)) *
        (hpRiemannThetaDifferentialKernel u : ℂ)) =
      ∑ n ∈ Finset.range N, hpThetaPhiComplexMomentTerm n z := by
  have hterm (n : ℕ) :
      (fun u : ℝ => ((z * (u : ℂ)) ^ (2 * n) /
        (Nat.factorial (2 * n) : ℂ)) * (hpRiemannThetaDifferentialKernel u : ℂ)) =
      (fun u : ℝ => (z ^ (2 * n) / (Nat.factorial (2 * n) : ℂ)) *
        ((u ^ (2 * n) * hpRiemannThetaDifferentialKernel u : ℝ) : ℂ)) := by
    funext u
    push_cast
    rw [mul_pow]
    ring
  have hint (n : ℕ) : Integrable
      (fun u : ℝ => ((z * (u : ℂ)) ^ (2 * n) /
        (Nat.factorial (2 * n) : ℂ)) * (hpRiemannThetaDifferentialKernel u : ℂ))
      (volume.restrict (Set.Ioi 0)) := by
    rw [hterm n]
    exact (hpThetaPhi_evenMoment_integrableOn n).ofReal.const_mul _
  simp_rw [hpThetaPhiComplexCoshPartial, Finset.sum_mul]
  rw [integral_finsetSum (Finset.range N) (fun n _ => hint n)]
  apply Finset.sum_congr rfl
  intro n hn
  rw [hterm n, integral_const_mul, integral_complex_ofReal]
  rfl

theorem hpRiemannXiCritical_complexMomentSeries_tendsto (z : ℂ) :
    Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.range N, hpThetaPhiComplexMomentTerm n z)
      atTop (𝓝 (hpRiemannXiCritical (z * Complex.I))) := by
  simpa only [hpThetaPhi_complexCoshPartial_integral_eq_moments] using
    hpRiemannXiCritical_complexCoshPartial_integral_tendsto z

theorem hpThetaPhi_realMomentSeries_summable (t : ℝ) :
    Summable (fun n : ℕ =>
      (t ^ (2 * n) / (Nat.factorial (2 * n) : ℝ)) * hpThetaPhiEvenMoment n) := by
  have hnonneg (n : ℕ) :
      0 ≤ (t ^ (2 * n) / (Nat.factorial (2 * n) : ℝ)) *
        hpThetaPhiEvenMoment n := by
    have hm := hpThetaPhi_evenMoment_nonneg n
    rw [pow_mul]
    positivity
  apply (summable_iff_not_tendsto_nat_atTop_of_nonneg hnonneg).2
  intro htop
  let L : ℝ := ∫ u : ℝ in Set.Ioi 0,
    Real.cosh (t * u) * hpRiemannThetaDifferentialKernel u
  have hlim := hpThetaPhi_evenMoment_series_tendsto t
  have hlt : ∀ᶠ N : ℕ in atTop,
      (∑ n ∈ Finset.range N,
        (t ^ (2 * n) / (Nat.factorial (2 * n) : ℝ)) * hpThetaPhiEvenMoment n) < L + 1 :=
    hlim.eventually (gt_mem_nhds (show L < L + 1 by linarith))
  have hge := htop.eventually_ge_atTop (L + 1)
  obtain ⟨N, hnlt, hnge⟩ := (hlt.and hge).exists
  linarith

theorem hpThetaPhi_complexMomentTerm_norm (n : ℕ) (z : ℂ) :
    ‖hpThetaPhiComplexMomentTerm n z‖ =
      (‖z‖ ^ (2 * n) / (Nat.factorial (2 * n) : ℝ)) * hpThetaPhiEvenMoment n := by
  simp only [hpThetaPhiComplexMomentTerm, norm_mul, norm_div, norm_pow,
    Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (hpThetaPhi_evenMoment_nonneg n)]

theorem hpThetaPhi_complexMomentSeries_summable_norm (z : ℂ) :
    Summable (fun n : ℕ => ‖hpThetaPhiComplexMomentTerm n z‖) := by
  simpa only [hpThetaPhi_complexMomentTerm_norm] using
    hpThetaPhi_realMomentSeries_summable ‖z‖

theorem hpRiemannXiCritical_complexMomentSeries_hasSum (z : ℂ) :
    HasSum (fun n : ℕ => hpThetaPhiComplexMomentTerm n z)
      (hpRiemannXiCritical (z * Complex.I)) := by
  exact (hasSum_iff_tendsto_nat_of_summable_norm
    (hpThetaPhi_complexMomentSeries_summable_norm z)).2
      (hpRiemannXiCritical_complexMomentSeries_tendsto z)

theorem hpThetaJensenGamma_complex_series_term (n : ℕ) (z : ℂ) :
    (hpThetaJensenGamma n : ℂ) * z ^ (2 * n) / (Nat.factorial n : ℂ) =
      hpThetaPhiComplexMomentTerm n z := by
  have hn : (Nat.factorial n : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  have h2n : (Nat.factorial (2 * n) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (2 * n)
  unfold hpThetaJensenGamma hpThetaPhiComplexMomentTerm
  push_cast
  field_simp [hn, h2n]

theorem hpRiemannXiCritical_complexJensenSeries_hasSum (z : ℂ) :
    HasSum
      (fun n : ℕ => (hpThetaJensenGamma n : ℂ) * z ^ (2 * n) /
        (Nat.factorial n : ℂ))
      (hpRiemannXiCritical (z * Complex.I)) := by
  simpa only [hpThetaJensenGamma_complex_series_term] using
    hpRiemannXiCritical_complexMomentSeries_hasSum z

theorem hpThetaJensen_complexSeries_summable_norm (z : ℂ) :
    Summable (fun n : ℕ =>
      ‖(hpThetaJensenGamma n : ℂ) * z ^ (2 * n) / (Nat.factorial n : ℂ)‖) := by
  simpa only [hpThetaJensenGamma_complex_series_term] using
    hpThetaPhi_complexMomentSeries_summable_norm z

theorem hpRiemannXiCritical_eq_complexJensenSeries (z : ℂ) :
    hpRiemannXiCritical (z * Complex.I) =
      ∑' n : ℕ, (hpThetaJensenGamma n : ℂ) * z ^ (2 * n) /
        (Nat.factorial n : ℂ) :=
  (hpRiemannXiCritical_complexJensenSeries_hasSum z).tsum_eq.symm

#print axioms hpThetaPhi_evenMoment_nonneg
#print axioms hpThetaPhi_complexCoshPartial_integral_eq_moments
#print axioms hpRiemannXiCritical_complexMomentSeries_tendsto
#print axioms hpThetaPhi_realMomentSeries_summable
#print axioms hpThetaPhi_complexMomentTerm_norm
#print axioms hpThetaPhi_complexMomentSeries_summable_norm
#print axioms hpRiemannXiCritical_complexMomentSeries_hasSum
#print axioms hpThetaJensenGamma_complex_series_term
#print axioms hpRiemannXiCritical_complexJensenSeries_hasSum
#print axioms hpThetaJensen_complexSeries_summable_norm
#print axioms hpRiemannXiCritical_eq_complexJensenSeries
end HodgeProofHP
