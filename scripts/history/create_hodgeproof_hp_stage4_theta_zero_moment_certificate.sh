#!/usr/bin/env bash
set -euo pipefail

command -v lake >/dev/null || {
  echo "ERROR: lake is not available."
  exit 1
}

lake build HodgeProofHP.Stage4ThetaTraceEnergyCertificate
lake build HodgeProofHP.Stage4ThetaPhiMomentIntegrability

target="HodgeProofHP/Stage4ThetaZeroMomentCertificate.lean"

if [ -f "$target" ]; then
  cp "$target" "$target.before_create_$(date +%Y%m%d_%H%M%S)_$$"
fi

cat > "$target" <<'LEAN'
import HodgeProofHP.Stage4ThetaTraceEnergyCertificate
import HodgeProofHP.Stage4ThetaPhiMomentIntegrability

/-!
A certified lower bound for the zeroth moment of the theta
differential kernel, using the existing interval certificates.
-/

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace HodgeProofHP

open MeasureTheory

theorem hpThetaPhi_finite_interval_lower_sum_le_momentZero
    (t : Finset ℕ) (l r q : ℕ → ℝ)
    (hl : ∀ i ∈ t, 0 ≤ l i)
    (hlr : ∀ i ∈ t, l i ≤ r i)
    (hdis : ∀ i ∈ t, ∀ j ∈ t, i ≠ j →
      Disjoint (Set.Ioo (l i) (r i))
        (Set.Ioo (l j) (r j)))
    (hbound : ∀ i ∈ t, ∀ u ∈ Set.Ioo (l i) (r i),
      q i ≤ hpRiemannThetaDifferentialKernel u) :
    (∑ i ∈ t, q i * (r i - l i)) ≤
      hpThetaPhiMomentZero := by
  classical
  have hint : ∀ i ∈ t,
      IntegrableOn hpRiemannThetaDifferentialKernel
        (Set.Ioo (l i) (r i)) := by
    intro i hi
    apply hpThetaPhi_integrableOn.mono_set
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
        hpRiemannThetaDifferentialKernel u) =
      ∑ i ∈ t, ∫ u : ℝ in Set.Ioo (l i) (r i),
        hpRiemannThetaDifferentialKernel u := by
    exact integral_biUnion_finset t
      (fun i hi => measurableSet_Ioo) hpair hint
  have hinterval : ∀ i ∈ t,
      q i * (r i - l i) ≤
        ∫ u : ℝ in Set.Ioo (l i) (r i),
          hpRiemannThetaDifferentialKernel u := by
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
          hpRiemannThetaDifferentialKernel u := by
    apply Finset.sum_le_sum
    intro i hi
    exact hinterval i hi
  have hmono :
      (∫ u : ℝ in ⋃ i ∈ t, Set.Ioo (l i) (r i),
        hpRiemannThetaDifferentialKernel u) ≤
      ∫ u : ℝ in Set.Ioi 0,
        hpRiemannThetaDifferentialKernel u := by
    apply setIntegral_mono_set hpThetaPhi_integrableOn
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      exact le_of_lt
        (hpThetaPhi_pos_on_nonnegative u (le_of_lt hu))
    · apply Filter.Eventually.of_forall
      intro u hu
      change 0 < u
      rcases Set.mem_iUnion.mp hu with ⟨i, hu⟩
      rcases Set.mem_iUnion.mp hu with ⟨hi, hui⟩
      exact lt_of_le_of_lt (hl i hi) hui.1
  unfold hpThetaPhiMomentZero
  calc
    _ ≤ ∑ i ∈ t, ∫ u : ℝ in Set.Ioo (l i) (r i),
        hpRiemannThetaDifferentialKernel u := hsum
    _ = ∫ u : ℝ in ⋃ i ∈ t, Set.Ioo (l i) (r i),
        hpRiemannThetaDifferentialKernel u := hunion.symm
    _ ≤ ∫ u : ℝ in Set.Ioi 0,
        hpRiemannThetaDifferentialKernel u := hmono

theorem hpThetaPhiMomentZero_gt_nine_twentieths :
    (9 / 20 : ℝ) < hpThetaPhiMomentZero := by
  classical
  have hl : ∀ i ∈ Finset.range 100,
      0 ≤ hpThetaTraceCertificateLeft i := by
    intro i hi
    unfold hpThetaTraceCertificateLeft
    positivity
  have hlr : ∀ i ∈ Finset.range 100,
      hpThetaTraceCertificateLeft i ≤
        hpThetaTraceCertificateRight i := by
    intro i hi
    unfold hpThetaTraceCertificateLeft hpThetaTraceCertificateRight
    linarith
  have hdis : ∀ i ∈ Finset.range 100, ∀ j ∈ Finset.range 100,
      i ≠ j →
      Disjoint
        (Set.Ioo (hpThetaTraceCertificateLeft i)
          (hpThetaTraceCertificateRight i))
        (Set.Ioo (hpThetaTraceCertificateLeft j)
          (hpThetaTraceCertificateRight j)) := by
    intro i hi j hj hij
    by_cases hlt : i < j
    · apply hpThetaTrace_intervals_disjoint
      unfold hpThetaTraceCertificateLeft hpThetaTraceCertificateRight
      apply div_le_div_of_nonneg_right _ (by norm_num)
      exact_mod_cast Nat.succ_le_of_lt hlt
    · apply Disjoint.symm
      apply hpThetaTrace_intervals_disjoint
      unfold hpThetaTraceCertificateLeft hpThetaTraceCertificateRight
      apply div_le_div_of_nonneg_right _ (by norm_num)
      have hji : j < i := by omega
      exact_mod_cast Nat.succ_le_of_lt hji
  have hbound : ∀ i ∈ Finset.range 100,
      ∀ u ∈ Set.Ioo (hpThetaTraceCertificateLeft i)
        (hpThetaTraceCertificateRight i),
      hpThetaTraceCertificateLower i ≤
        hpRiemannThetaDifferentialKernel u := by
    intro i hi u hu
    have hu0 : 0 ≤ u := by
      exact le_trans (hl i hi) (le_of_lt hu.1)
    calc
      hpThetaTraceCertificateLower i ≤
          hpThetaTraceEndpointLower
            (hpThetaTraceCertificateLeft i)
            (hpThetaTraceCertificateRight i) :=
        hpThetaTraceCertificateLower_endpoint i (Finset.mem_range.mp hi)
      _ ≤ hpThetaTraceFirstTerm u :=
        hpThetaTraceEndpointLower_le_firstTerm _ _ _
          (hl i hi) (le_of_lt hu.1) (le_of_lt hu.2)
      _ ≤ hpRiemannThetaDifferentialKernel u :=
        hpThetaTraceFirstTerm_le_phi u hu0
  have hsum := hpThetaPhi_finite_interval_lower_sum_le_momentZero
    (Finset.range 100)
    hpThetaTraceCertificateLeft hpThetaTraceCertificateRight
    hpThetaTraceCertificateLower hl hlr hdis hbound
  have hnumeric :
      (9 / 20 : ℝ) <
        ∑ i ∈ Finset.range 100,
          hpThetaTraceCertificateLower i *
            (hpThetaTraceCertificateRight i -
              hpThetaTraceCertificateLeft i) := by
    norm_num [hpThetaTraceCertificateLeft,
      hpThetaTraceCertificateRight, hpThetaTraceCertificateLower,
      Finset.sum_range_succ]
  exact lt_of_lt_of_le hnumeric hsum

#print axioms hpThetaPhi_finite_interval_lower_sum_le_momentZero
#print axioms hpThetaPhiMomentZero_gt_nine_twentieths

end HodgeProofHP
LEAN

lake env lean "$target"
lake build HodgeProofHP.Stage4ThetaZeroMomentCertificate

echo "PASS: Stage4ThetaZeroMomentCertificate"
