import HodgeProofHP.Stage7ThetaJensenLocallyUniformConvergence
import HodgeProofHP.Stage7ThetaJensenHurwitzDisk
import HodgeProofHP.Stage6ThetaJensenRiemannHypothesisEquivalence
import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# Conditional RH consequence of all-degree Jensen real zeros

The generating function is analytic and not identically zero, so its zeros
are isolated. The reciprocal maximum-modulus disk step transfers nonreal-zero
exclusion from the rescaled polynomial family to the limit. This yields RH
only under the explicit all-degree real-zero hypothesis below. That hypothesis
is not proved, and no reverse Jensen criterion is asserted in this module.
-/

noncomputable section
open Filter Set Metric
open scoped Topology

namespace HodgeProofHP

/-- Unproved: every zero of every unshifted Jensen polynomial is real. -/
def hpThetaJensenAllDegreesRealZeros : Prop :=
  ∀ (d : ℕ) (w : ℂ),
    (hpThetaJensenPolynomial d 0).eval₂ Complex.ofRealHom w = 0 → w.im = 0

/-- Unproved: all positive-degree rescaled approximants exclude nonreal zeros. -/
def hpThetaJensenRescaledNonrealZeroExclusion : Prop :=
  ∀ d : ℕ, 0 < d → ∀ w : ℂ, w.im ≠ 0 →
    hpThetaJensenRescaledPolynomialValue d w ≠ 0

theorem hpThetaJensenGeneratingFunction_punctured_ne_zero (a : ℂ) :
    ∀ᶠ z in 𝓝[≠] a, hpThetaJensenGeneratingFunction z ≠ 0 := by
  have han := hpThetaJensenGeneratingFunction_analyticAt a
  rcases han.eventually_eq_zero_or_eventually_ne_zero with hzero | hne
  · exfalso
    have hglobal := hpThetaJensenGeneratingFunction_analyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero
        PreconnectedSpace.isPreconnected_univ (mem_univ a) hzero
    exact hpThetaJensenGeneratingFunction_zero_ne_zero (hglobal (mem_univ (0 : ℂ)))
  · exact hne

theorem hpThetaJensenGeneratingFunction_exists_nonreal_disk
    (a : ℂ) (ha : a.im ≠ 0) :
    ∃ r : ℝ, 0 < r ∧
      (∀ z ∈ closedBall a r, z.im ≠ 0) ∧
      (∀ z ∈ frontier (ball a r), hpThetaJensenGeneratingFunction z ≠ 0) := by
  have hopen : IsOpen {z : ℂ | z.im ≠ 0} :=
    isOpen_ne_fun Complex.continuous_im continuous_const
  obtain ⟨δ, hδ, hδset⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds ha)
  obtain ⟨ε, hε, hεset⟩ := Metric.mem_nhdsWithin_iff.mp
    (hpThetaJensenGeneratingFunction_punctured_ne_zero a)
  let r : ℝ := min ε δ / 2
  have hr : 0 < r := div_pos (lt_min hε hδ) (by norm_num)
  have hrε : r < ε := by
    dsimp [r]
    have h := min_le_left ε δ
    linarith
  have hrδ : r < δ := by
    dsimp [r]
    have h := min_le_right ε δ
    linarith
  refine ⟨r, hr, ?_, ?_⟩
  · intro z hz
    exact hδset (lt_of_le_of_lt hz hrδ)
  · intro z hz
    have hsp : z ∈ sphere a r := frontier_ball_subset_sphere hz
    have hza : z ≠ a := ne_of_mem_sphere hsp (ne_of_gt hr)
    apply hεset
    refine ⟨?_, ?_⟩
    · change dist z a < ε
      exact (mem_sphere.mp hsp).trans_lt hrε
    · simpa only [mem_compl_iff, mem_singleton_iff] using hza

theorem hpThetaJensen_nonrealZeroExclusion_of_rescaledFamily
    (h : hpThetaJensenRescaledNonrealZeroExclusion) :
    hpThetaJensenNonrealZeroExclusion := by
  intro a ha
  obtain ⟨r, hr, hnonreal, hboundary⟩ :=
    hpThetaJensenGeneratingFunction_exists_nonreal_disk a ha
  apply hpComplexDisk_uniformLimit_ne_zero
    hpThetaJensenRescaledPolynomialValue hpThetaJensenGeneratingFunction a r hr
    (hpThetaJensenRescaledPolynomialValue_tendstoUniformlyOn_compact
      (closedBall a r) (isCompact_closedBall a r))
    (hpThetaJensenGeneratingFunction_analyticOnNhd.continuousOn.mono (subset_univ _))
    hboundary
  filter_upwards [eventually_ge_atTop 1] with d hd
  refine ⟨(hpThetaJensenRescaledPolynomialValue_differentiable d).diffContOnCl, ?_⟩
  intro z hz
  exact h d (by omega) z (hnonreal z hz)

theorem hpThetaJensen_rescaledFamily_of_allDegreesRealZeros
    (h : hpThetaJensenAllDegreesRealZeros) :
    hpThetaJensenRescaledNonrealZeroExclusion := by
  intro d hd w hw hzero
  have hq : (w / (d : ℂ)).im = 0 :=
    h d (w / (d : ℂ)) hzero
  have hd0 : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hd)
  have heq : w = (d : ℂ) * (w / (d : ℂ)) := by
    field_simp
  apply hw
  rw [heq, Complex.mul_im, hq]
  simp

/-- Conditional only: the rescaled-family hypothesis remains unproved. -/
theorem hpThetaJensen_RH_of_rescaledFamily
    (h : hpThetaJensenRescaledNonrealZeroExclusion) : RiemannHypothesis :=
  hpThetaJensen_RH_of_nonrealZeroExclusion
    (hpThetaJensen_nonrealZeroExclusion_of_rescaledFamily h)

/-- Conditional only: this is not a proof of the all-degree real-zero hypothesis. -/
theorem hpThetaJensen_RH_of_allDegreesRealZeros
    (h : hpThetaJensenAllDegreesRealZeros) : RiemannHypothesis :=
  hpThetaJensen_RH_of_rescaledFamily
    (hpThetaJensen_rescaledFamily_of_allDegreesRealZeros h)

#print axioms hpThetaJensenGeneratingFunction_punctured_ne_zero
#print axioms hpThetaJensenGeneratingFunction_exists_nonreal_disk
#print axioms hpThetaJensen_nonrealZeroExclusion_of_rescaledFamily
#print axioms hpThetaJensen_rescaledFamily_of_allDegreesRealZeros
#print axioms hpThetaJensen_RH_of_rescaledFamily
#print axioms hpThetaJensen_RH_of_allDegreesRealZeros

end HodgeProofHP
