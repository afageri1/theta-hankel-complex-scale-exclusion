import HodgeProofHP.Stage4ThetaTraceFiniteEnergy
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
Interval lower bounds for the first theta term's weighted square energy.
Pointwise estimates remain explicit hypotheses until separately certified.
-/

namespace HodgeProofHP

open MeasureTheory

theorem hpThetaTraceFirstTerm_interval_weighted_sq_lower
    (l r q : ℝ) (hl : 0 ≤ l) (hq : 0 ≤ q)
    (hbound : ∀ u ∈ Set.Ioo l r, q ≤ hpThetaTraceFirstTerm u)
    (u : ℝ) (hu : u ∈ Set.Ioo l r) :
    l * q ^ 2 ≤ u * hpThetaTraceFirstTerm u ^ 2 := by
  have hterm : q ≤ hpThetaTraceFirstTerm u := hbound u hu
  have hterm0 : 0 ≤ hpThetaTraceFirstTerm u :=
    le_trans hq hterm
  have hsq : q ^ 2 ≤ hpThetaTraceFirstTerm u ^ 2 := by
    nlinarith
  calc
    l * q ^ 2 ≤ l * hpThetaTraceFirstTerm u ^ 2 :=
      mul_le_mul_of_nonneg_left hsq hl
    _ ≤ u * hpThetaTraceFirstTerm u ^ 2 :=
      mul_le_mul_of_nonneg_right (le_of_lt hu.1) (sq_nonneg _)

theorem hpThetaTraceFirstTerm_interval_energy_lower
    (l r q : ℝ) (hl : 0 ≤ l) (hlr : l ≤ r) (hq : 0 ≤ q)
    (hbound : ∀ u ∈ Set.Ioo l r, q ≤ hpThetaTraceFirstTerm u) :
    l * q ^ 2 * (r - l) ≤
      ∫ u : ℝ in Set.Ioo l r, u * hpThetaTraceFirstTerm u ^ 2 := by
  have hfinite : volume (Set.Ioo l r) ≠ ⊤ := by
    simp
  have h :=
    setIntegral_ge_of_const_le_real
      (μ := volume)
      (s := Set.Ioo l r)
      (f := fun u : ℝ => u * hpThetaTraceFirstTerm u ^ 2)
      (c := l * q ^ 2)
      measurableSet_Ioo hfinite
      (fun u hu =>
        hpThetaTraceFirstTerm_interval_weighted_sq_lower
          l r q hl hq hbound u hu)
      (hpThetaTraceFirstTerm_energy_integrableOn_Ioo l r hl)
  rw [Real.volume_real_Ioo_of_le hlr] at h
  exact h

theorem hpThetaTraceFirstTerm_interval_lower_le_totalEnergy
    (l r q : ℝ) (hl : 0 ≤ l) (hlr : l ≤ r) (hq : 0 ≤ q)
    (hbound : ∀ u ∈ Set.Ioo l r, q ≤ hpThetaTraceFirstTerm u) :
    l * q ^ 2 * (r - l) ≤ hpThetaFirstTraceEnergy := by
  exact le_trans
    (hpThetaTraceFirstTerm_interval_energy_lower l r q hl hlr hq hbound)
    (hpThetaTraceFirstTerm_finite_energy_le l r hl)

#print axioms hpThetaTraceFirstTerm_interval_weighted_sq_lower
#print axioms hpThetaTraceFirstTerm_interval_energy_lower
#print axioms hpThetaTraceFirstTerm_interval_lower_le_totalEnergy

end HodgeProofHP
