import HodgeProofHP.Stage4ThetaTraceFirstIntervalCertificate

/-!
Adding energy lower certificates on disjoint positive intervals.
Disjointness prevents counting the same contribution twice.
-/

namespace HodgeProofHP

open MeasureTheory

theorem hpThetaTrace_intervals_disjoint
    (a b c d : ℝ) (hbc : b ≤ c) :
    Disjoint (Set.Ioo a b) (Set.Ioo c d) := by
  apply Set.disjoint_left.mpr
  intro u hu hv
  have hub : u < b := hu.2
  have hcu : c < u := hv.1
  linarith

theorem hpThetaTrace_two_interval_energy_le
    (a b c d : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hbc : b ≤ c) :
    (∫ u : ℝ in Set.Ioo a b, u * hpThetaTraceFirstTerm u ^ 2) +
      (∫ u : ℝ in Set.Ioo c d, u * hpThetaTraceFirstTerm u ^ 2) ≤
      hpThetaFirstTraceEnergy := by
  have hab :=
    hpThetaTraceFirstTerm_energy_integrableOn_Ioo a b ha
  have hcd :=
    hpThetaTraceFirstTerm_energy_integrableOn_Ioo c d hc
  have hdis := hpThetaTrace_intervals_disjoint a b c d hbc
  have hunion :
      (∫ u : ℝ in Set.Ioo a b ∪ Set.Ioo c d,
        u * hpThetaTraceFirstTerm u ^ 2) =
      (∫ u : ℝ in Set.Ioo a b, u * hpThetaTraceFirstTerm u ^ 2) +
        (∫ u : ℝ in Set.Ioo c d, u * hpThetaTraceFirstTerm u ^ 2) :=
    setIntegral_union hdis measurableSet_Ioo hab hcd
  have hmono :
      (∫ u : ℝ in Set.Ioo a b ∪ Set.Ioo c d,
        u * hpThetaTraceFirstTerm u ^ 2) ≤
      ∫ u : ℝ in Set.Ioi 0, u * hpThetaTraceFirstTerm u ^ 2 := by
    apply setIntegral_mono_set
      hpThetaTraceFirstTerm_weighted_sq_integrableOn
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      exact mul_nonneg (le_of_lt hu) (sq_nonneg _)
    · apply Filter.Eventually.of_forall
      intro u hu
      change 0 < u
      rcases hu with hu | hu
      · exact lt_of_le_of_lt ha hu.1
      · exact lt_of_le_of_lt hc hu.1
  calc
    _ = ∫ u : ℝ in Set.Ioo a b ∪ Set.Ioo c d,
        u * hpThetaTraceFirstTerm u ^ 2 := hunion.symm
    _ ≤ ∫ u : ℝ in Set.Ioi 0,
        u * hpThetaTraceFirstTerm u ^ 2 := hmono
    _ ≤ hpThetaFirstTraceEnergy :=
      hpThetaTraceFirstTerm_energy_le

theorem hpThetaTrace_two_interval_lower_le_totalEnergy
    (a b c d q₁ q₂ : ℝ)
    (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hab : a ≤ b) (hcd : c ≤ d) (hbc : b ≤ c)
    (hq₁ : 0 ≤ q₁) (hq₂ : 0 ≤ q₂)
    (hbound₁ : ∀ u ∈ Set.Ioo a b, q₁ ≤ hpThetaTraceFirstTerm u)
    (hbound₂ : ∀ u ∈ Set.Ioo c d, q₂ ≤ hpThetaTraceFirstTerm u) :
    a * q₁ ^ 2 * (b - a) + c * q₂ ^ 2 * (d - c) ≤
      hpThetaFirstTraceEnergy := by
  have h₁ :=
    hpThetaTraceFirstTerm_interval_energy_lower
      a b q₁ ha hab hq₁ hbound₁
  have h₂ :=
    hpThetaTraceFirstTerm_interval_energy_lower
      c d q₂ hc hcd hq₂ hbound₂
  exact le_trans (add_le_add h₁ h₂)
    (hpThetaTrace_two_interval_energy_le a b c d ha hc hbc)

#print axioms hpThetaTrace_intervals_disjoint
#print axioms hpThetaTrace_two_interval_energy_le
#print axioms hpThetaTrace_two_interval_lower_le_totalEnergy

end HodgeProofHP
