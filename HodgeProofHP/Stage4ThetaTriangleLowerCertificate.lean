import HodgeProofHP.Stage4ThetaZeroMomentRefinedCertificate

/-!
A numerical lower bound for the triangularly weighted theta integral.
This file reuses the verified fourth-moment endpoint certificates.
-/

set_option maxRecDepth 10000
-- Explicit finite rational sums require additional elaboration resources.
set_option maxHeartbeats 0

noncomputable section

namespace HodgeProofHP

open MeasureTheory

def hpThetaTriangleWeight (u : ℝ) : ℝ :=
  max 0 (min u (1 / 2 - u))

def hpThetaTriangleIntegrand (u : ℝ) : ℝ :=
  hpThetaTriangleWeight u * hpRiemannThetaDifferentialKernel u

def hpThetaTriangleMoment : ℝ :=
  ∫ u : ℝ in Set.Ioi 0, hpThetaTriangleIntegrand u

def hpThetaHankelTriangleRayleighLower : ℝ :=
  4 * hpThetaTriangleMoment

theorem hpThetaTriangleWeight_nonneg (u : ℝ) :
    0 ≤ hpThetaTriangleWeight u :=
  le_max_left _ _

theorem hpThetaTriangleWeight_le_quarter (u : ℝ) :
    hpThetaTriangleWeight u ≤ 1 / 4 := by
  have hmin : min u (1 / 2 - u) ≤ (1 / 4 : ℝ) := by
    by_cases hu : u ≤ 1 / 4
    · exact le_trans (min_le_left _ _) hu
    · exact le_trans (min_le_right _ _) (by linarith)
  exact max_le (by norm_num) hmin

theorem hpThetaTriangleWeight_continuous :
    Continuous hpThetaTriangleWeight := by
  unfold hpThetaTriangleWeight
  exact continuous_const.max
    (continuous_id.min (continuous_const.sub continuous_id))

theorem hpThetaTriangleWeight_norm_le (u : ℝ) :
    ‖hpThetaTriangleWeight u‖ ≤ (1 / 4 : ℝ) := by
  rw [Real.norm_eq_abs, abs_of_nonneg (hpThetaTriangleWeight_nonneg u)]
  exact hpThetaTriangleWeight_le_quarter u

theorem hpThetaTriangleIntegrand_nonneg (u : ℝ) (hu : 0 ≤ u) :
    0 ≤ hpThetaTriangleIntegrand u := by
  exact mul_nonneg (hpThetaTriangleWeight_nonneg u)
    (le_of_lt (hpThetaPhi_pos_on_nonnegative u hu))

theorem hpThetaTriangleIntegrand_integrableOn :
    IntegrableOn hpThetaTriangleIntegrand (Set.Ioi 0) := by
  apply (hpThetaPhi_integrableOn.norm.const_mul (1 / 4 : ℝ)).mono'
  · exact hpThetaTriangleWeight_continuous.aestronglyMeasurable.mul
      hpThetaPhi_integrableOn.aestronglyMeasurable
  · apply Filter.Eventually.of_forall
    intro u
    change ‖hpThetaTriangleWeight u *
      hpRiemannThetaDifferentialKernel u‖ ≤
      (1 / 4 : ℝ) * ‖hpRiemannThetaDifferentialKernel u‖
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right
      (hpThetaTriangleWeight_norm_le u) (norm_nonneg _)

def hpThetaTriangleCertificateWeight (i : ℕ) : ℝ :=
  max 0 (min (hpThetaFourthCertificateLeft i)
    (1 / 2 - hpThetaFourthCertificateRight i))

theorem hpThetaTriangleCertificateWeight_nonneg (i : ℕ) :
    0 ≤ hpThetaTriangleCertificateWeight i :=
  le_max_left _ _

theorem hpThetaTriangleCertificateWeight_le
    (i : ℕ) (u : ℝ)
    (hl : hpThetaFourthCertificateLeft i ≤ u)
    (hr : u ≤ hpThetaFourthCertificateRight i) :
    hpThetaTriangleCertificateWeight i ≤ hpThetaTriangleWeight u := by
  unfold hpThetaTriangleCertificateWeight hpThetaTriangleWeight
  exact max_le_max le_rfl
    (min_le_min hl (sub_le_sub_left hr (1 / 2 : ℝ)))

theorem hpThetaTriangle_finite_interval_lower_sum_le_moment
    (t : Finset ℕ) (l r q : ℕ → ℝ)
    (hl : ∀ i ∈ t, 0 ≤ l i)
    (hlr : ∀ i ∈ t, l i ≤ r i)
    (hdis : ∀ i ∈ t, ∀ j ∈ t, i ≠ j →
      Disjoint (Set.Ioo (l i) (r i))
        (Set.Ioo (l j) (r j)))
    (hbound : ∀ i ∈ t, ∀ u ∈ Set.Ioo (l i) (r i),
      q i ≤ hpThetaTriangleIntegrand u) :
    (∑ i ∈ t, q i * (r i - l i)) ≤
      hpThetaTriangleMoment := by
  classical
  have hint : ∀ i ∈ t,
      IntegrableOn hpThetaTriangleIntegrand
        (Set.Ioo (l i) (r i)) := by
    intro i hi
    apply hpThetaTriangleIntegrand_integrableOn.mono_set
    intro u hu
    exact lt_of_le_of_lt (hl i hi) hu.1
  have hpair : (↑t : Set ℕ).Pairwise
      (fun i j =>
        Disjoint (Set.Ioo (l i) (r i))
          (Set.Ioo (l j) (r j))) := by
    intro i hi j hj hij
    exact hdis i hi j hj hij
  have hunion :
      (∫ u : ℝ in ⋃ i ∈ t, Set.Ioo (l i) (r i),
        hpThetaTriangleIntegrand u) =
      ∑ i ∈ t, ∫ u : ℝ in Set.Ioo (l i) (r i),
        hpThetaTriangleIntegrand u := by
    exact integral_biUnion_finset t
      (fun i hi => measurableSet_Ioo) hpair hint
  have hinterval : ∀ i ∈ t,
      q i * (r i - l i) ≤
        ∫ u : ℝ in Set.Ioo (l i) (r i),
          hpThetaTriangleIntegrand u := by
    intro i hi
    have hfinite :
        volume (Set.Ioo (l i) (r i)) ≠ ⊤ := by
      simp
    have h := setIntegral_ge_of_const_le_real
      measurableSet_Ioo hfinite
      (hbound i hi) (hint i hi)
    rw [Real.volume_real_Ioo_of_le (hlr i hi)] at h
    exact h
  have hsum :
      (∑ i ∈ t, q i * (r i - l i)) ≤
        ∑ i ∈ t, ∫ u : ℝ in Set.Ioo (l i) (r i),
          hpThetaTriangleIntegrand u := by
    apply Finset.sum_le_sum
    intro i hi
    exact hinterval i hi
  have hmono :
      (∫ u : ℝ in ⋃ i ∈ t, Set.Ioo (l i) (r i),
        hpThetaTriangleIntegrand u) ≤
      ∫ u : ℝ in Set.Ioi 0,
        hpThetaTriangleIntegrand u := by
    apply setIntegral_mono_set hpThetaTriangleIntegrand_integrableOn
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      exact hpThetaTriangleIntegrand_nonneg u (le_of_lt hu)
    · apply Filter.Eventually.of_forall
      intro u hu
      change 0 < u
      rcases Set.mem_iUnion.mp hu with ⟨i, hu⟩
      rcases Set.mem_iUnion.mp hu with ⟨hi, hui⟩
      exact lt_of_le_of_lt (hl i hi) hui.1
  unfold hpThetaTriangleMoment
  calc
    _ ≤ ∑ i ∈ t, ∫ u : ℝ in Set.Ioo (l i) (r i),
        hpThetaTriangleIntegrand u := hsum
    _ = ∫ u : ℝ in ⋃ i ∈ t, Set.Ioo (l i) (r i),
        hpThetaTriangleIntegrand u := hunion.symm
    _ ≤ ∫ u : ℝ in Set.Ioi 0,
        hpThetaTriangleIntegrand u := hmono


theorem hpThetaHankelTriangleRayleighLower_gt :
    (117 / 500 : ℝ) < hpThetaHankelTriangleRayleighLower := by
  classical
  have hl : ∀ i ∈ Finset.range 200,
      0 ≤ hpThetaFourthCertificateLeft i := by
    intro i hi
    unfold hpThetaFourthCertificateLeft
    positivity
  have hlr : ∀ i ∈ Finset.range 200,
      hpThetaFourthCertificateLeft i ≤
        hpThetaFourthCertificateRight i := by
    intro i hi
    unfold hpThetaFourthCertificateLeft hpThetaFourthCertificateRight
    linarith
  have hdis : ∀ i ∈ Finset.range 200, ∀ j ∈ Finset.range 200,
      i ≠ j →
      Disjoint
        (Set.Ioo (hpThetaFourthCertificateLeft i)
          (hpThetaFourthCertificateRight i))
        (Set.Ioo (hpThetaFourthCertificateLeft j)
          (hpThetaFourthCertificateRight j)) := by
    intro i hi j hj hij
    by_cases hlt : i < j
    · apply hpThetaTrace_intervals_disjoint
      unfold hpThetaFourthCertificateLeft hpThetaFourthCertificateRight
      apply div_le_div_of_nonneg_right _ (by norm_num)
      exact_mod_cast Nat.succ_le_of_lt hlt
    · apply Disjoint.symm
      apply hpThetaTrace_intervals_disjoint
      unfold hpThetaFourthCertificateLeft hpThetaFourthCertificateRight
      apply div_le_div_of_nonneg_right _ (by norm_num)
      have hji : j < i := by omega
      exact_mod_cast Nat.succ_le_of_lt hji
  have hbound : ∀ i ∈ Finset.range 200,
      ∀ u ∈ Set.Ioo (hpThetaFourthCertificateLeft i)
        (hpThetaFourthCertificateRight i),
      hpThetaFourthCertificateLower i *
        hpThetaTriangleCertificateWeight i ≤
          hpThetaTriangleIntegrand u := by
    intro i hi u hu
    have hu0 : 0 ≤ u := le_trans (hl i hi) hu.1.le
    have hi400 : i < 400 := by
      have hi200 := Finset.mem_range.mp hi
      omega
    have hp :
        hpThetaFourthCertificateLower i ≤
          hpRiemannThetaDifferentialKernel u := by
      calc
        hpThetaFourthCertificateLower i ≤
            hpThetaTraceEndpointLower
              (hpThetaFourthCertificateLeft i)
              (hpThetaFourthCertificateRight i) :=
          hpThetaFourthCertificateLower_endpoint i hi400
        _ ≤ hpThetaTraceFirstTerm u :=
          hpThetaTraceEndpointLower_le_firstTerm _ _ _
            (hl i hi) hu.1.le hu.2.le
        _ ≤ hpRiemannThetaDifferentialKernel u :=
          hpThetaTraceFirstTerm_le_phi u hu0
    have hw :=
      hpThetaTriangleCertificateWeight_le i u hu.1.le hu.2.le
    have hprod := mul_le_mul hw hp
      (hpThetaFourthCertificateLower_nonneg i)
      (hpThetaTriangleWeight_nonneg u)
    simpa only [hpThetaTriangleIntegrand, mul_comm] using hprod
  have hsum := hpThetaTriangle_finite_interval_lower_sum_le_moment
    (Finset.range 200)
    hpThetaFourthCertificateLeft hpThetaFourthCertificateRight
    (fun i => hpThetaFourthCertificateLower i *
      hpThetaTriangleCertificateWeight i)
    hl hlr hdis hbound
  have hnumeric :
      (117 / 2000 : ℝ) <
        ∑ i ∈ Finset.range 200,
          (hpThetaFourthCertificateLower i *
            hpThetaTriangleCertificateWeight i) *
          (hpThetaFourthCertificateRight i -
            hpThetaFourthCertificateLeft i) := by
    -- Expand the sum before normalizing its rational terms.
    simp only [Finset.sum_range_succ]
    norm_num (config := { maxSteps := 2000000 })
      [hpThetaFourthCertificateLeft,
       hpThetaFourthCertificateRight,
       hpThetaFourthCertificateLower,
       hpThetaTriangleCertificateWeight]
  have hm := lt_of_lt_of_le hnumeric hsum
  unfold hpThetaHankelTriangleRayleighLower
  linarith

#print axioms hpThetaTriangleIntegrand_integrableOn
#print axioms hpThetaHankelTriangleRayleighLower_gt

end HodgeProofHP
