import HodgeProofHP.Stage4ThetaTraceDisjointEnergy

/-!
Finite sums of energy certificates on pairwise disjoint positive intervals.
-/

namespace HodgeProofHP

open MeasureTheory

theorem hpThetaTrace_finite_interval_energy_sum_le
    (t : Finset ℕ) (l r : ℕ → ℝ)
    (hl : ∀ i ∈ t, 0 ≤ l i)
    (hdis : ∀ i ∈ t, ∀ j ∈ t, i ≠ j →
      Disjoint (Set.Ioo (l i) (r i)) (Set.Ioo (l j) (r j))) :
    (∑ i ∈ t, ∫ u : ℝ in Set.Ioo (l i) (r i),
      u * hpThetaTraceFirstTerm u ^ 2) ≤ hpThetaFirstTraceEnergy := by
  classical
  have hpair : (↑t : Set ℕ).Pairwise
      (fun i j =>
        Disjoint (Set.Ioo (l i) (r i)) (Set.Ioo (l j) (r j))) := by
    intro i hi j hj hij
    exact hdis i hi j hj hij
  have hunion :
      (∫ u : ℝ in ⋃ i ∈ t, Set.Ioo (l i) (r i),
        u * hpThetaTraceFirstTerm u ^ 2) =
      ∑ i ∈ t, ∫ u : ℝ in Set.Ioo (l i) (r i),
        u * hpThetaTraceFirstTerm u ^ 2 := by
    exact integral_biUnion_finset t
      (fun i hi => measurableSet_Ioo) hpair
      (fun i hi =>
        hpThetaTraceFirstTerm_energy_integrableOn_Ioo
          (l i) (r i) (hl i hi))
  have hmono :
      (∫ u : ℝ in ⋃ i ∈ t, Set.Ioo (l i) (r i),
        u * hpThetaTraceFirstTerm u ^ 2) ≤
      ∫ u : ℝ in Set.Ioi 0, u * hpThetaTraceFirstTerm u ^ 2 := by
    apply setIntegral_mono_set
      hpThetaTraceFirstTerm_weighted_sq_integrableOn
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      exact mul_nonneg (le_of_lt hu) (sq_nonneg _)
    · apply Filter.Eventually.of_forall
      intro u hu
      change 0 < u
      rcases Set.mem_iUnion.mp hu with ⟨i, hu⟩
      rcases Set.mem_iUnion.mp hu with ⟨hi, hui⟩
      exact lt_of_le_of_lt (hl i hi) hui.1
  calc
    _ = ∫ u : ℝ in ⋃ i ∈ t, Set.Ioo (l i) (r i),
        u * hpThetaTraceFirstTerm u ^ 2 := hunion.symm
    _ ≤ ∫ u : ℝ in Set.Ioi 0,
        u * hpThetaTraceFirstTerm u ^ 2 := hmono
    _ ≤ hpThetaFirstTraceEnergy :=
      hpThetaTraceFirstTerm_energy_le

theorem hpThetaTrace_finite_interval_lower_sum_le
    (t : Finset ℕ) (l r q : ℕ → ℝ)
    (hl : ∀ i ∈ t, 0 ≤ l i)
    (hlr : ∀ i ∈ t, l i ≤ r i)
    (hq : ∀ i ∈ t, 0 ≤ q i)
    (hdis : ∀ i ∈ t, ∀ j ∈ t, i ≠ j →
      Disjoint (Set.Ioo (l i) (r i)) (Set.Ioo (l j) (r j)))
    (hbound : ∀ i ∈ t, ∀ u ∈ Set.Ioo (l i) (r i),
      q i ≤ hpThetaTraceFirstTerm u) :
    (∑ i ∈ t, l i * q i ^ 2 * (r i - l i)) ≤
      hpThetaFirstTraceEnergy := by
  classical
  have hsum :
      (∑ i ∈ t, l i * q i ^ 2 * (r i - l i)) ≤
      ∑ i ∈ t, ∫ u : ℝ in Set.Ioo (l i) (r i),
        u * hpThetaTraceFirstTerm u ^ 2 := by
    apply Finset.sum_le_sum
    intro i hi
    exact hpThetaTraceFirstTerm_interval_energy_lower
      (l i) (r i) (q i)
      (hl i hi) (hlr i hi) (hq i hi) (hbound i hi)
  exact le_trans hsum
    (hpThetaTrace_finite_interval_energy_sum_le t l r hl hdis)

#print axioms hpThetaTrace_finite_interval_energy_sum_le
#print axioms hpThetaTrace_finite_interval_lower_sum_le

end HodgeProofHP
