import HodgeProofHP.Stage7ThetaJensenConditionalRiemannHypothesis

/-!
# Cofinal Jensen real-zero hypotheses suffice for RH

The same disk argument applies to any sequence of good degrees tending to
infinity. Thus arbitrarily large real-rooted unshifted Jensen polynomials
suffice for RH. Contrapositively, if RH is false, every sufficiently large
unshifted degree has a nonreal zero. No cofinal real-zero hypothesis is proved.
-/

noncomputable section
open Filter Set Metric
open scoped Topology

namespace HodgeProofHP

def hpThetaJensenDegreeRealZeros (d : ℕ) : Prop :=
  ∀ w : ℂ,
    (hpThetaJensenPolynomial d 0).eval₂ Complex.ofRealHom w = 0 → w.im = 0

/-- Unproved: good unshifted degrees are unbounded. -/
def hpThetaJensenCofinalRealZeros : Prop :=
  ∀ N : ℕ, ∃ d : ℕ, N ≤ d ∧ hpThetaJensenDegreeRealZeros d

theorem hpThetaJensen_rescaled_ne_zero_of_degreeRealZeros
    (d : ℕ) (hd : 0 < d) (h : hpThetaJensenDegreeRealZeros d)
    (w : ℂ) (hw : w.im ≠ 0) :
    hpThetaJensenRescaledPolynomialValue d w ≠ 0 := by
  intro hzero
  have hq : (w / (d : ℂ)).im = 0 := h (w / (d : ℂ)) hzero
  have hd0 : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hd)
  have heq : w = (d : ℂ) * (w / (d : ℂ)) := by field_simp
  apply hw
  rw [heq, Complex.mul_im, hq]
  simp

theorem hpThetaJensen_nonrealZeroExclusion_of_cofinalRealZeros
    (h : hpThetaJensenCofinalRealZeros) : hpThetaJensenNonrealZeroExclusion := by
  classical
  choose k hk using (fun n : ℕ => h (n + 1))
  have hseq : Tendsto k atTop atTop :=
    tendsto_atTop_mono
      (fun n => (Nat.le_succ n).trans (hk n).1) tendsto_id
  intro a ha
  obtain ⟨r, hr, hnonreal, hboundary⟩ :=
    hpThetaJensenGeneratingFunction_exists_nonreal_disk a ha
  have hconv : TendstoUniformlyOn
      (fun n : ℕ => hpThetaJensenRescaledPolynomialValue (k n))
      hpThetaJensenGeneratingFunction atTop (closedBall a r) := by
    intro u hu
    exact hseq.eventually
      (hpThetaJensenRescaledPolynomialValue_tendstoUniformlyOn_compact
        (closedBall a r) (isCompact_closedBall a r) u hu)
  apply hpComplexDisk_uniformLimit_ne_zero
    (fun n : ℕ => hpThetaJensenRescaledPolynomialValue (k n))
    hpThetaJensenGeneratingFunction a r hr hconv
    (hpThetaJensenGeneratingFunction_analyticOnNhd.continuousOn.mono (subset_univ _))
    hboundary
  apply Eventually.of_forall
  intro n
  refine ⟨(hpThetaJensenRescaledPolynomialValue_differentiable (k n)).diffContOnCl, ?_⟩
  intro z hz
  have hkpos : 0 < k n := by have hkn := (hk n).1; omega
  exact hpThetaJensen_rescaled_ne_zero_of_degreeRealZeros
    (k n) hkpos (hk n).2 z (hnonreal z hz)

/-- Conditional only: unbounded good degrees have not been established. -/
theorem hpThetaJensen_RH_of_cofinalRealZeros
    (h : hpThetaJensenCofinalRealZeros) : RiemannHypothesis :=
  hpThetaJensen_RH_of_nonrealZeroExclusion
    (hpThetaJensen_nonrealZeroExclusion_of_cofinalRealZeros h)

/-- Conditional on failure of RH, not an assertion that RH is false. -/
theorem hpThetaJensen_eventually_nonrealZero_of_not_RH
    (hRH : ¬ RiemannHypothesis) :
    ∃ N : ℕ, ∀ d : ℕ, N ≤ d → ∃ w : ℂ, w.im ≠ 0 ∧
      (hpThetaJensenPolynomial d 0).eval₂ Complex.ofRealHom w = 0 := by
  classical
  have hnot : ¬ hpThetaJensenCofinalRealZeros :=
    fun h => hRH (hpThetaJensen_RH_of_cofinalRealZeros h)
  unfold hpThetaJensenCofinalRealZeros at hnot
  push_neg at hnot
  obtain ⟨N, hN⟩ := hnot
  refine ⟨N, ?_⟩
  intro d hd
  have hbad := hN d hd
  unfold hpThetaJensenDegreeRealZeros at hbad
  push_neg at hbad
  obtain ⟨w, hzero, him⟩ := hbad
  exact ⟨w, him, hzero⟩

#print axioms hpThetaJensen_rescaled_ne_zero_of_degreeRealZeros
#print axioms hpThetaJensen_nonrealZeroExclusion_of_cofinalRealZeros
#print axioms hpThetaJensen_RH_of_cofinalRealZeros
#print axioms hpThetaJensen_eventually_nonrealZero_of_not_RH

end HodgeProofHP
