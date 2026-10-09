import HodgeProofHP.Stage6ThetaJensenXiImaginaryExpansion
import Mathlib.Tactic

/-!
# Complex cosh partial sums and dominated convergence

The real exponential envelope also controls complex parameters.
The integrals of complex partial sums converge to xi(i*z) for every z.
Extracting the integrated moment coefficients and proving absolute
summability of the resulting moment series are subsequent obligations.
-/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology
namespace HodgeProofHP

def hpThetaPhiComplexCoshPartial (N : ℕ) (w : ℂ) : ℂ :=
  ∑ n ∈ Finset.range N, w ^ (2 * n) / (Nat.factorial (2 * n) : ℂ)

theorem hpThetaPhi_complexCoshPartial_norm_le
    (N : ℕ) (z : ℂ) (u : ℝ) (hu : 0 ≤ u) :
    ‖hpThetaPhiComplexCoshPartial N (z * (u : ℂ))‖ ≤
      Real.exp (‖z‖ * u) := by
  have hsum :
      ‖hpThetaPhiComplexCoshPartial N (z * (u : ℂ))‖ ≤
        hpThetaPhiCoshPartial N (‖z‖ * u) := by
    unfold hpThetaPhiComplexCoshPartial hpThetaPhiCoshPartial
    calc
      ‖∑ n ∈ Finset.range N,
          (z * (u : ℂ)) ^ (2 * n) / (Nat.factorial (2 * n) : ℂ)‖ ≤
          ∑ n ∈ Finset.range N,
            ‖(z * (u : ℂ)) ^ (2 * n) / (Nat.factorial (2 * n) : ℂ)‖ :=
        norm_sum_le _ _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro n hn
        simp only [norm_div, norm_pow, norm_mul, Complex.norm_natCast,
          Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu]
  have hreal := hpThetaPhi_coshPartial_norm_le N ‖z‖ u hu
  rw [Real.norm_eq_abs,
    abs_of_nonneg (hpThetaPhi_coshPartial_nonneg N (‖z‖ * u)),
    abs_of_nonneg (norm_nonneg z)] at hreal
  exact hsum.trans hreal

theorem hpThetaPhi_complexCoshEnvelope_integrableOn (z : ℂ) :
    IntegrableOn
      (fun u : ℝ => Real.exp (‖z‖ * u) *
        |hpRiemannThetaDifferentialKernel u|)
      (Set.Ioi 0) volume := by
  simpa only [abs_of_nonneg (norm_nonneg z)] using
    hpThetaPhi_coshEnvelope_integrableOn ‖z‖

theorem hpThetaPhi_complexCoshPartial_integrableOn (N : ℕ) (z : ℂ) :
    IntegrableOn
      (fun u : ℝ => hpThetaPhiComplexCoshPartial N (z * (u : ℂ)) *
        (hpRiemannThetaDifferentialKernel u : ℂ))
      (Set.Ioi 0) volume := by
  have hkernel := hpRiemannThetaDifferentialKernel_continuous
  have hcont : Continuous
      (fun u : ℝ => hpThetaPhiComplexCoshPartial N (z * (u : ℂ)) *
        (hpRiemannThetaDifferentialKernel u : ℂ)) := by
    unfold hpThetaPhiComplexCoshPartial
    fun_prop
  apply (hpThetaPhi_complexCoshEnvelope_integrableOn z).mono'
    hcont.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right
    (hpThetaPhi_complexCoshPartial_norm_le N z u (le_of_lt hu))
    (abs_nonneg _)

theorem hpThetaPhi_complexCoshPartial_weighted_tendsto (z : ℂ) (u : ℝ) :
    Tendsto
      (fun N : ℕ => hpThetaPhiComplexCoshPartial N (z * (u : ℂ)) *
        (hpRiemannThetaDifferentialKernel u : ℂ))
      atTop (𝓝 (Complex.cosh (z * (u : ℂ)) *
        (hpRiemannThetaDifferentialKernel u : ℂ))) := by
  simpa only [hpThetaPhiComplexCoshPartial, Finset.sum_mul] using
    ((Complex.hasSum_cosh (z * (u : ℂ))).mul_right
      (hpRiemannThetaDifferentialKernel u : ℂ)).tendsto_sum_nat

theorem hpRiemannXiCritical_mul_I_eq_complexCosh_integral (z : ℂ) :
    hpRiemannXiCritical (z * Complex.I) =
      ∫ u : ℝ in Set.Ioi 0, Complex.cosh (z * (u : ℂ)) *
        (hpRiemannThetaDifferentialKernel u : ℂ) := by
  rw [hpRiemannXiCritical_eq_differentialKernel_cosine_integral]
  apply integral_congr_ae
  filter_upwards [] with u
  change (hpRiemannThetaDifferentialKernel u : ℂ) *
    Complex.cos ((z * Complex.I) * (u : ℂ)) = _
  have harg : (z * Complex.I) * (u : ℂ) = (z * (u : ℂ)) * Complex.I := by
    ring
  rw [harg, Complex.cos_mul_I]
  ring

theorem hpRiemannXiCritical_complexCoshPartial_integral_tendsto (z : ℂ) :
    Tendsto
      (fun N : ℕ => ∫ u : ℝ in Set.Ioi 0,
        hpThetaPhiComplexCoshPartial N (z * (u : ℂ)) *
          (hpRiemannThetaDifferentialKernel u : ℂ))
      atTop (𝓝 (hpRiemannXiCritical (z * Complex.I))) := by
  rw [hpRiemannXiCritical_mul_I_eq_complexCosh_integral]
  apply tendsto_integral_of_dominated_convergence
    (fun u : ℝ => Real.exp (‖z‖ * u) *
      |hpRiemannThetaDifferentialKernel u|)
  · intro N
    exact (hpThetaPhi_complexCoshPartial_integrableOn N z).aestronglyMeasurable
  · exact hpThetaPhi_complexCoshEnvelope_integrableOn z
  · intro N
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right
      (hpThetaPhi_complexCoshPartial_norm_le N z u (le_of_lt hu))
      (abs_nonneg _)
  · exact Filter.Eventually.of_forall
      (fun u => hpThetaPhi_complexCoshPartial_weighted_tendsto z u)

#print axioms hpThetaPhi_complexCoshPartial_norm_le
#print axioms hpThetaPhi_complexCoshEnvelope_integrableOn
#print axioms hpThetaPhi_complexCoshPartial_integrableOn
#print axioms hpThetaPhi_complexCoshPartial_weighted_tendsto
#print axioms hpRiemannXiCritical_mul_I_eq_complexCosh_integral
#print axioms hpRiemannXiCritical_complexCoshPartial_integral_tendsto
end HodgeProofHP
