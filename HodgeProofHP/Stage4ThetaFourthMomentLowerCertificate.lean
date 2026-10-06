import HodgeProofHP.Stage4ThetaFourthMomentCertificateBatch00
import HodgeProofHP.Stage4ThetaFourthMomentCertificateBatch01
import HodgeProofHP.Stage4ThetaFourthMomentCertificateBatch02
import HodgeProofHP.Stage4ThetaFourthMomentCertificateBatch03
import HodgeProofHP.Stage4ThetaFourthMomentCertificateBatch04
import HodgeProofHP.Stage4ThetaFourthMomentCertificateBatch05
import HodgeProofHP.Stage4ThetaFourthMomentCertificateBatch06
import HodgeProofHP.Stage4ThetaFourthMomentCertificateBatch07
import HodgeProofHP.Stage4ThetaFourthMomentCertificateBatch08
import HodgeProofHP.Stage4ThetaFourthMomentCertificateBatch09
import HodgeProofHP.Stage4ThetaFourthMomentCertificateBatch10
import HodgeProofHP.Stage4ThetaFourthMomentCertificateBatch11
import HodgeProofHP.Stage4ThetaFourthMomentCertificateBatch12
import HodgeProofHP.Stage4ThetaFourthMomentCertificateBatch13
import HodgeProofHP.Stage4ThetaFourthMomentCertificateBatch14
import HodgeProofHP.Stage4ThetaFourthMomentCertificateBatch15
import HodgeProofHP.Stage4ThetaFourthMomentCertificateBatch16
import HodgeProofHP.Stage4ThetaFourthMomentCertificateBatch17
import HodgeProofHP.Stage4ThetaFourthMomentCertificateBatch18
import HodgeProofHP.Stage4ThetaFourthMomentCertificateBatch19

/-!
The fourth-moment lower bound, assembled from independently compiled
interval certificate batches.
-/

-- The final rational sum has four hundred terms.
set_option maxHeartbeats 0
set_option maxRecDepth 10000

noncomputable section

namespace HodgeProofHP

open MeasureTheory


theorem hpThetaFourthCertificateLower_endpoint
    (i : ℕ) (hi : i < 400) :
    hpThetaFourthCertificateLower i ≤
      hpThetaTraceEndpointLower
        (hpThetaFourthCertificateLeft i)
        (hpThetaFourthCertificateRight i) := by
  by_cases h0 : i < 20
  · exact hpThetaFourthCertificateLower_endpoint_batch_0
      i (by omega) h0
  by_cases h1 : i < 40
  · exact hpThetaFourthCertificateLower_endpoint_batch_1
      i (by omega) h1
  by_cases h2 : i < 60
  · exact hpThetaFourthCertificateLower_endpoint_batch_2
      i (by omega) h2
  by_cases h3 : i < 80
  · exact hpThetaFourthCertificateLower_endpoint_batch_3
      i (by omega) h3
  by_cases h4 : i < 100
  · exact hpThetaFourthCertificateLower_endpoint_batch_4
      i (by omega) h4
  by_cases h5 : i < 120
  · exact hpThetaFourthCertificateLower_endpoint_batch_5
      i (by omega) h5
  by_cases h6 : i < 140
  · exact hpThetaFourthCertificateLower_endpoint_batch_6
      i (by omega) h6
  by_cases h7 : i < 160
  · exact hpThetaFourthCertificateLower_endpoint_batch_7
      i (by omega) h7
  by_cases h8 : i < 180
  · exact hpThetaFourthCertificateLower_endpoint_batch_8
      i (by omega) h8
  by_cases h9 : i < 200
  · exact hpThetaFourthCertificateLower_endpoint_batch_9
      i (by omega) h9
  by_cases h10 : i < 220
  · exact hpThetaFourthCertificateLower_endpoint_batch_10
      i (by omega) h10
  by_cases h11 : i < 240
  · exact hpThetaFourthCertificateLower_endpoint_batch_11
      i (by omega) h11
  by_cases h12 : i < 260
  · exact hpThetaFourthCertificateLower_endpoint_batch_12
      i (by omega) h12
  by_cases h13 : i < 280
  · exact hpThetaFourthCertificateLower_endpoint_batch_13
      i (by omega) h13
  by_cases h14 : i < 300
  · exact hpThetaFourthCertificateLower_endpoint_batch_14
      i (by omega) h14
  by_cases h15 : i < 320
  · exact hpThetaFourthCertificateLower_endpoint_batch_15
      i (by omega) h15
  by_cases h16 : i < 340
  · exact hpThetaFourthCertificateLower_endpoint_batch_16
      i (by omega) h16
  by_cases h17 : i < 360
  · exact hpThetaFourthCertificateLower_endpoint_batch_17
      i (by omega) h17
  by_cases h18 : i < 380
  · exact hpThetaFourthCertificateLower_endpoint_batch_18
      i (by omega) h18
  exact hpThetaFourthCertificateLower_endpoint_batch_19
    i (by omega) hi

theorem hpThetaFourthCertificate_finite_lower_sum_le_moment
    (t : Finset ℕ) (l r q : ℕ → ℝ)
    (hl : ∀ i ∈ t, 0 ≤ l i)
    (hlr : ∀ i ∈ t, l i ≤ r i)
    (hdis : ∀ i ∈ t, ∀ j ∈ t, i ≠ j →
      Disjoint (Set.Ioo (l i) (r i))
        (Set.Ioo (l j) (r j)))
    (hbound : ∀ i ∈ t, ∀ u ∈ Set.Ioo (l i) (r i),
      q i ≤ hpThetaFourthCertificateIntegrand u) :
    (∑ i ∈ t, q i * (r i - l i)) ≤
      hpThetaPhiMomentFour := by
  classical
  have hint : ∀ i ∈ t,
      IntegrableOn hpThetaFourthCertificateIntegrand
        (Set.Ioo (l i) (r i)) := by
    intro i hi
    apply hpThetaPhi_fourthMoment_integrableOn.mono_set
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
        hpThetaFourthCertificateIntegrand u) =
      ∑ i ∈ t, ∫ u : ℝ in Set.Ioo (l i) (r i),
        hpThetaFourthCertificateIntegrand u := by
    exact integral_biUnion_finset t
      (fun i hi => measurableSet_Ioo) hpair hint
  have hinterval : ∀ i ∈ t,
      q i * (r i - l i) ≤
        ∫ u : ℝ in Set.Ioo (l i) (r i),
          hpThetaFourthCertificateIntegrand u := by
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
          hpThetaFourthCertificateIntegrand u := by
    apply Finset.sum_le_sum
    intro i hi
    exact hinterval i hi
  have hmono :
      (∫ u : ℝ in ⋃ i ∈ t, Set.Ioo (l i) (r i),
        hpThetaFourthCertificateIntegrand u) ≤
      ∫ u : ℝ in Set.Ioi 0,
        hpThetaFourthCertificateIntegrand u := by
    apply setIntegral_mono_set hpThetaPhi_fourthMoment_integrableOn
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      exact hpThetaFourthCertificateIntegrand_nonneg u (le_of_lt hu)
    · apply Filter.Eventually.of_forall
      intro u hu
      change 0 < u
      rcases Set.mem_iUnion.mp hu with ⟨i, hu⟩
      rcases Set.mem_iUnion.mp hu with ⟨hi, hui⟩
      exact lt_of_le_of_lt (hl i hi) hui.1
  unfold hpThetaPhiMomentFour
  calc
    _ ≤ ∑ i ∈ t, ∫ u : ℝ in Set.Ioo (l i) (r i),
        hpThetaFourthCertificateIntegrand u := hsum
    _ = ∫ u : ℝ in ⋃ i ∈ t, Set.Ioo (l i) (r i),
        hpThetaFourthCertificateIntegrand u := hunion.symm
    _ ≤ ∫ u : ℝ in Set.Ioi 0,
        hpThetaFourthCertificateIntegrand u := hmono



theorem hpThetaPhiMomentFour_gt_twentySeven_tenThousandths :
    (27 / 10000 : ℝ) < hpThetaPhiMomentFour := by
  classical
  have hl : ∀ i ∈ Finset.range 400,
      0 ≤ hpThetaFourthCertificateLeft i := by
    intro i hi
    unfold hpThetaFourthCertificateLeft
    positivity
  have hlr : ∀ i ∈ Finset.range 400,
      hpThetaFourthCertificateLeft i ≤
        hpThetaFourthCertificateRight i := by
    intro i hi
    unfold hpThetaFourthCertificateLeft hpThetaFourthCertificateRight
    linarith
  have hdis : ∀ i ∈ Finset.range 400, ∀ j ∈ Finset.range 400,
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
      have hnat : i + 1 ≤ j := Nat.succ_le_of_lt hlt
      exact_mod_cast hnat
    · apply Disjoint.symm
      apply hpThetaTrace_intervals_disjoint
      unfold hpThetaFourthCertificateLeft hpThetaFourthCertificateRight
      apply div_le_div_of_nonneg_right _ (by norm_num)
      have hji : j < i := by omega
      have hnat : j + 1 ≤ i := Nat.succ_le_of_lt hji
      exact_mod_cast hnat
  have hbound : ∀ i ∈ Finset.range 400,
      ∀ u ∈ Set.Ioo (hpThetaFourthCertificateLeft i)
        (hpThetaFourthCertificateRight i),
      hpThetaFourthCertificateLower i *
          hpThetaFourthCertificateLeft i ^ 4 ≤
        hpThetaFourthCertificateIntegrand u := by
    intro i hi u hu
    have hu0 : 0 ≤ u :=
      le_trans (hl i hi) (le_of_lt hu.1)
    have hp :
        hpThetaFourthCertificateLower i ≤
          hpRiemannThetaDifferentialKernel u := by
      calc
        _ ≤ hpThetaTraceEndpointLower
            (hpThetaFourthCertificateLeft i)
            (hpThetaFourthCertificateRight i) :=
          hpThetaFourthCertificateLower_endpoint i (Finset.mem_range.mp hi)
        _ ≤ hpThetaTraceFirstTerm u :=
          hpThetaTraceEndpointLower_le_firstTerm _ _ _
            (hl i hi) (le_of_lt hu.1) (le_of_lt hu.2)
        _ ≤ hpRiemannThetaDifferentialKernel u :=
          hpThetaTraceFirstTerm_le_phi u hu0
    have hpow :
        hpThetaFourthCertificateLeft i ^ 4 ≤ u ^ 4 :=
      pow_le_pow_left₀ (hl i hi) (le_of_lt hu.1) 4
    have hprod := mul_le_mul hpow hp
      (hpThetaFourthCertificateLower_nonneg i)
      (pow_nonneg hu0 4)
    simpa only [hpThetaFourthCertificateIntegrand, mul_comm] using hprod
  have hsum := hpThetaFourthCertificate_finite_lower_sum_le_moment
    (Finset.range 400)
    hpThetaFourthCertificateLeft hpThetaFourthCertificateRight
    (fun i => hpThetaFourthCertificateLower i *
      hpThetaFourthCertificateLeft i ^ 4)
    hl hlr hdis hbound
  have hnumeric :
      (27 / 10000 : ℝ) <
        ∑ i ∈ Finset.range 400,
          (hpThetaFourthCertificateLower i *
            hpThetaFourthCertificateLeft i ^ 4) *
          (hpThetaFourthCertificateRight i -
            hpThetaFourthCertificateLeft i) := by
    -- Expand the finite sum separately from rational normalization.
    simp only [Finset.sum_range_succ]
    norm_num (config := { maxSteps := 2000000 })
      [hpThetaFourthCertificateLeft,
       hpThetaFourthCertificateRight,
       hpThetaFourthCertificateLower]
  exact lt_of_lt_of_le hnumeric hsum

#print axioms hpThetaPhiMomentFour_gt_twentySeven_tenThousandths

end HodgeProofHP
