import HodgeProofHP.Stage4ThetaFourthMomentLowerCertificate
import HodgeProofHP.Stage4ThetaZeroMomentCertificate

/-!
A refined numerical lower bound for the zeroth theta moment,
reusing the four hundred verified endpoint certificates.
-/

noncomputable section

namespace HodgeProofHP

open MeasureTheory

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- The explicit rational sum contains four hundred certified intervals.
theorem hpThetaPhiMomentZero_gt_twelve_twentyFifths :
    (12 / 25 : ℝ) < hpThetaPhiMomentZero := by
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
      exact_mod_cast Nat.succ_le_of_lt hlt
    · apply Disjoint.symm
      apply hpThetaTrace_intervals_disjoint
      unfold hpThetaFourthCertificateLeft hpThetaFourthCertificateRight
      apply div_le_div_of_nonneg_right _ (by norm_num)
      have hji : j < i := by omega
      exact_mod_cast Nat.succ_le_of_lt hji
  have hbound : ∀ i ∈ Finset.range 400,
      ∀ u ∈ Set.Ioo (hpThetaFourthCertificateLeft i)
        (hpThetaFourthCertificateRight i),
      hpThetaFourthCertificateLower i ≤
        hpRiemannThetaDifferentialKernel u := by
    intro i hi u hu
    have hu0 : 0 ≤ u := by
      exact le_trans (hl i hi) (le_of_lt hu.1)
    calc
      hpThetaFourthCertificateLower i ≤
          hpThetaTraceEndpointLower
            (hpThetaFourthCertificateLeft i)
            (hpThetaFourthCertificateRight i) :=
        hpThetaFourthCertificateLower_endpoint i (Finset.mem_range.mp hi)
      _ ≤ hpThetaTraceFirstTerm u :=
        hpThetaTraceEndpointLower_le_firstTerm _ _ _
          (hl i hi) (le_of_lt hu.1) (le_of_lt hu.2)
      _ ≤ hpRiemannThetaDifferentialKernel u :=
        hpThetaTraceFirstTerm_le_phi u hu0
  have hsum := hpThetaPhi_finite_interval_lower_sum_le_momentZero
    (Finset.range 400)
    hpThetaFourthCertificateLeft hpThetaFourthCertificateRight
    hpThetaFourthCertificateLower hl hlr hdis hbound
  have hnumeric :
      (12 / 25 : ℝ) <
        ∑ i ∈ Finset.range 400,
          hpThetaFourthCertificateLower i *
            (hpThetaFourthCertificateRight i -
              hpThetaFourthCertificateLeft i) := by
    -- Expand the sum before normalizing its rational terms.
    simp only [Finset.sum_range_succ]
    norm_num (config := { maxSteps := 2000000 })
      [hpThetaFourthCertificateLeft,
       hpThetaFourthCertificateRight,
       hpThetaFourthCertificateLower]
  exact lt_of_lt_of_le hnumeric hsum


#print axioms hpThetaPhiMomentZero_gt_twelve_twentyFifths

end HodgeProofHP
