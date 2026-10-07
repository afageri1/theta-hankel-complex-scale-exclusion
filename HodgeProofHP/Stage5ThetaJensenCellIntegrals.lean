import HodgeProofHP.Stage5ThetaJensenAllCellCertificates
import HodgeProofHP.Stage4ThetaPhiMomentIntegrability
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-!
# Integrating the 1600 Jensen cell certificates

For moment orders 0, 2, and 4, each certified kernel rectangle
bounds its actual weighted integral on the open cell interval.
All numerical kernel hypotheses in the batch theorems are discharged
by the previously checked cell certificates. Summation and the
identification with full moments are the next proof obligation.
-/

noncomputable section
open MeasureTheory
namespace HodgeProofHP

theorem hpThetaJensen_powerIntegrand_integrableOn
    (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
    IntegrableOn (fun u : ℝ => u ^ m * hpRiemannThetaDifferentialKernel u)
      (Set.Ioi 0) volume := by
  rcases hm with rfl | rfl | rfl
  · simpa using hpThetaPhi_integrableOn
  · exact hpThetaPhi_secondMoment_integrableOn
  · exact hpThetaPhi_fourthMoment_integrableOn

theorem hpThetaJensen_cellIntegral_bounds
    (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4)
    (l r L U : ℝ) (hl : 0 ≤ l) (hlr : l ≤ r) (hL : 0 ≤ L)
    (hbound : ∀ u ∈ Set.Icc l r,
      L ≤ hpRiemannThetaDifferentialKernel u ∧
        hpRiemannThetaDifferentialKernel u ≤ U) :
    l ^ m * L * (r - l) ≤
        (∫ u : ℝ in Set.Ioo l r, u ^ m * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo l r, u ^ m * hpRiemannThetaDifferentialKernel u) ≤
        r ^ m * U * (r - l) := by
  have hint : IntegrableOn
      (fun u : ℝ => u ^ m * hpRiemannThetaDifferentialKernel u)
      (Set.Ioo l r) volume := by
    apply (hpThetaJensen_powerIntegrand_integrableOn m hm).mono_set
    intro u hu
    exact lt_of_le_of_lt hl hu.1
  have hfinite : volume (Set.Ioo l r) ≠ ⊤ := by simp
  have hlow : ∀ u ∈ Set.Ioo l r,
      l ^ m * L ≤ u ^ m * hpRiemannThetaDifferentialKernel u := by
    intro u hu
    have hu0 := le_trans hl (le_of_lt hu.1)
    have h := hbound u ⟨le_of_lt hu.1, le_of_lt hu.2⟩
    exact mul_le_mul (pow_le_pow_left₀ hl (le_of_lt hu.1) m)
      h.1 hL (pow_nonneg hu0 m)
  have hupp : ∀ u ∈ Set.Ioo l r,
      u ^ m * hpRiemannThetaDifferentialKernel u ≤ r ^ m * U := by
    intro u hu
    have hu0 := le_trans hl (le_of_lt hu.1)
    have h := hbound u ⟨le_of_lt hu.1, le_of_lt hu.2⟩
    exact mul_le_mul (pow_le_pow_left₀ hu0 (le_of_lt hu.2) m)
      h.2 (le_of_lt (hpThetaPhi_pos_on_nonnegative u hu0))
      (pow_nonneg (le_trans hl hlr) m)
  constructor
  · have h := setIntegral_ge_of_const_le_real
      measurableSet_Ioo hfinite hlow hint
    rw [Real.volume_real_Ioo_of_le hlr] at h
    exact h
  · have hneg : ∀ u ∈ Set.Ioo l r,
        -(r ^ m * U) ≤ -(u ^ m * hpRiemannThetaDifferentialKernel u) := by
      intro u hu
      exact neg_le_neg (hupp u hu)
    have h := setIntegral_ge_of_const_le_real
      measurableSet_Ioo hfinite hneg hint.neg
    rw [Real.volume_real_Ioo_of_le hlr, integral_neg] at h
    linarith

theorem hpThetaJensenCellsBatch000_cellIntegral_bounds
    (j : Fin 20) (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
    (((0 : ℝ) + (j.val : ℝ)) / 1600) ^ m * hpThetaJensenCellsBatch000Lower j.val *
        ((((0 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((0 : ℝ) + (j.val : ℝ)) / 1600)) ≤
      (∫ u : ℝ in Set.Ioo (((0 : ℝ) + (j.val : ℝ)) / 1600)
        (((0 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (((0 : ℝ) + (j.val : ℝ)) / 1600)
        (((0 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ≤
        (((0 : ℝ) + (j.val : ℝ) + 1) / 1600) ^ m * hpThetaJensenCellsBatch000Upper j.val *
          ((((0 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((0 : ℝ) + (j.val : ℝ)) / 1600)) := by
  apply hpThetaJensen_cellIntegral_bounds m hm
  · positivity
  · linarith
  · fin_cases j <;> norm_num [hpThetaJensenCellsBatch000Lower]
  · exact hpThetaJensenCellsBatch000_bounds j

theorem hpThetaJensenCellsBatch001_cellIntegral_bounds
    (j : Fin 20) (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
    (((20 : ℝ) + (j.val : ℝ)) / 1600) ^ m * hpThetaJensenCellsBatch001Lower j.val *
        ((((20 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((20 : ℝ) + (j.val : ℝ)) / 1600)) ≤
      (∫ u : ℝ in Set.Ioo (((20 : ℝ) + (j.val : ℝ)) / 1600)
        (((20 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (((20 : ℝ) + (j.val : ℝ)) / 1600)
        (((20 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ≤
        (((20 : ℝ) + (j.val : ℝ) + 1) / 1600) ^ m * hpThetaJensenCellsBatch001Upper j.val *
          ((((20 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((20 : ℝ) + (j.val : ℝ)) / 1600)) := by
  apply hpThetaJensen_cellIntegral_bounds m hm
  · positivity
  · linarith
  · fin_cases j <;> norm_num [hpThetaJensenCellsBatch001Lower]
  · exact hpThetaJensenCellsBatch001_bounds j

theorem hpThetaJensenCellsBatch002_cellIntegral_bounds
    (j : Fin 20) (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
    (((40 : ℝ) + (j.val : ℝ)) / 1600) ^ m * hpThetaJensenCellsBatch002Lower j.val *
        ((((40 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((40 : ℝ) + (j.val : ℝ)) / 1600)) ≤
      (∫ u : ℝ in Set.Ioo (((40 : ℝ) + (j.val : ℝ)) / 1600)
        (((40 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (((40 : ℝ) + (j.val : ℝ)) / 1600)
        (((40 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ≤
        (((40 : ℝ) + (j.val : ℝ) + 1) / 1600) ^ m * hpThetaJensenCellsBatch002Upper j.val *
          ((((40 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((40 : ℝ) + (j.val : ℝ)) / 1600)) := by
  apply hpThetaJensen_cellIntegral_bounds m hm
  · positivity
  · linarith
  · fin_cases j <;> norm_num [hpThetaJensenCellsBatch002Lower]
  · exact hpThetaJensenCellsBatch002_bounds j

theorem hpThetaJensenCellsBatch003_cellIntegral_bounds
    (j : Fin 20) (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
    (((60 : ℝ) + (j.val : ℝ)) / 1600) ^ m * hpThetaJensenCellsBatch003Lower j.val *
        ((((60 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((60 : ℝ) + (j.val : ℝ)) / 1600)) ≤
      (∫ u : ℝ in Set.Ioo (((60 : ℝ) + (j.val : ℝ)) / 1600)
        (((60 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (((60 : ℝ) + (j.val : ℝ)) / 1600)
        (((60 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ≤
        (((60 : ℝ) + (j.val : ℝ) + 1) / 1600) ^ m * hpThetaJensenCellsBatch003Upper j.val *
          ((((60 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((60 : ℝ) + (j.val : ℝ)) / 1600)) := by
  apply hpThetaJensen_cellIntegral_bounds m hm
  · positivity
  · linarith
  · fin_cases j <;> norm_num [hpThetaJensenCellsBatch003Lower]
  · exact hpThetaJensenCellsBatch003_bounds j

theorem hpThetaJensenCellsBatch004_cellIntegral_bounds
    (j : Fin 20) (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
    (((80 : ℝ) + (j.val : ℝ)) / 1600) ^ m * hpThetaJensenCellsBatch004Lower j.val *
        ((((80 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((80 : ℝ) + (j.val : ℝ)) / 1600)) ≤
      (∫ u : ℝ in Set.Ioo (((80 : ℝ) + (j.val : ℝ)) / 1600)
        (((80 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (((80 : ℝ) + (j.val : ℝ)) / 1600)
        (((80 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ≤
        (((80 : ℝ) + (j.val : ℝ) + 1) / 1600) ^ m * hpThetaJensenCellsBatch004Upper j.val *
          ((((80 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((80 : ℝ) + (j.val : ℝ)) / 1600)) := by
  apply hpThetaJensen_cellIntegral_bounds m hm
  · positivity
  · linarith
  · fin_cases j <;> norm_num [hpThetaJensenCellsBatch004Lower]
  · exact hpThetaJensenCellsBatch004_bounds j

theorem hpThetaJensenCellsBatch005_cellIntegral_bounds
    (j : Fin 20) (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
    (((100 : ℝ) + (j.val : ℝ)) / 1600) ^ m * hpThetaJensenCellsBatch005Lower j.val *
        ((((100 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((100 : ℝ) + (j.val : ℝ)) / 1600)) ≤
      (∫ u : ℝ in Set.Ioo (((100 : ℝ) + (j.val : ℝ)) / 1600)
        (((100 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (((100 : ℝ) + (j.val : ℝ)) / 1600)
        (((100 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ≤
        (((100 : ℝ) + (j.val : ℝ) + 1) / 1600) ^ m * hpThetaJensenCellsBatch005Upper j.val *
          ((((100 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((100 : ℝ) + (j.val : ℝ)) / 1600)) := by
  apply hpThetaJensen_cellIntegral_bounds m hm
  · positivity
  · linarith
  · fin_cases j <;> norm_num [hpThetaJensenCellsBatch005Lower]
  · exact hpThetaJensenCellsBatch005_bounds j

theorem hpThetaJensenCellsBatch006_cellIntegral_bounds
    (j : Fin 20) (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
    (((120 : ℝ) + (j.val : ℝ)) / 1600) ^ m * hpThetaJensenCellsBatch006Lower j.val *
        ((((120 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((120 : ℝ) + (j.val : ℝ)) / 1600)) ≤
      (∫ u : ℝ in Set.Ioo (((120 : ℝ) + (j.val : ℝ)) / 1600)
        (((120 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (((120 : ℝ) + (j.val : ℝ)) / 1600)
        (((120 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ≤
        (((120 : ℝ) + (j.val : ℝ) + 1) / 1600) ^ m * hpThetaJensenCellsBatch006Upper j.val *
          ((((120 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((120 : ℝ) + (j.val : ℝ)) / 1600)) := by
  apply hpThetaJensen_cellIntegral_bounds m hm
  · positivity
  · linarith
  · fin_cases j <;> norm_num [hpThetaJensenCellsBatch006Lower]
  · exact hpThetaJensenCellsBatch006_bounds j

theorem hpThetaJensenCellsBatch007_cellIntegral_bounds
    (j : Fin 20) (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
    (((140 : ℝ) + (j.val : ℝ)) / 1600) ^ m * hpThetaJensenCellsBatch007Lower j.val *
        ((((140 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((140 : ℝ) + (j.val : ℝ)) / 1600)) ≤
      (∫ u : ℝ in Set.Ioo (((140 : ℝ) + (j.val : ℝ)) / 1600)
        (((140 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (((140 : ℝ) + (j.val : ℝ)) / 1600)
        (((140 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ≤
        (((140 : ℝ) + (j.val : ℝ) + 1) / 1600) ^ m * hpThetaJensenCellsBatch007Upper j.val *
          ((((140 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((140 : ℝ) + (j.val : ℝ)) / 1600)) := by
  apply hpThetaJensen_cellIntegral_bounds m hm
  · positivity
  · linarith
  · fin_cases j <;> norm_num [hpThetaJensenCellsBatch007Lower]
  · exact hpThetaJensenCellsBatch007_bounds j

theorem hpThetaJensenCellsBatch008_cellIntegral_bounds
    (j : Fin 20) (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
    (((160 : ℝ) + (j.val : ℝ)) / 1600) ^ m * hpThetaJensenCellsBatch008Lower j.val *
        ((((160 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((160 : ℝ) + (j.val : ℝ)) / 1600)) ≤
      (∫ u : ℝ in Set.Ioo (((160 : ℝ) + (j.val : ℝ)) / 1600)
        (((160 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (((160 : ℝ) + (j.val : ℝ)) / 1600)
        (((160 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ≤
        (((160 : ℝ) + (j.val : ℝ) + 1) / 1600) ^ m * hpThetaJensenCellsBatch008Upper j.val *
          ((((160 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((160 : ℝ) + (j.val : ℝ)) / 1600)) := by
  apply hpThetaJensen_cellIntegral_bounds m hm
  · positivity
  · linarith
  · fin_cases j <;> norm_num [hpThetaJensenCellsBatch008Lower]
  · exact hpThetaJensenCellsBatch008_bounds j

theorem hpThetaJensenCellsBatch009_cellIntegral_bounds
    (j : Fin 20) (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
    (((180 : ℝ) + (j.val : ℝ)) / 1600) ^ m * hpThetaJensenCellsBatch009Lower j.val *
        ((((180 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((180 : ℝ) + (j.val : ℝ)) / 1600)) ≤
      (∫ u : ℝ in Set.Ioo (((180 : ℝ) + (j.val : ℝ)) / 1600)
        (((180 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (((180 : ℝ) + (j.val : ℝ)) / 1600)
        (((180 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ≤
        (((180 : ℝ) + (j.val : ℝ) + 1) / 1600) ^ m * hpThetaJensenCellsBatch009Upper j.val *
          ((((180 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((180 : ℝ) + (j.val : ℝ)) / 1600)) := by
  apply hpThetaJensen_cellIntegral_bounds m hm
  · positivity
  · linarith
  · fin_cases j <;> norm_num [hpThetaJensenCellsBatch009Lower]
  · exact hpThetaJensenCellsBatch009_bounds j

theorem hpThetaJensenCellsBatch010_cellIntegral_bounds
    (j : Fin 20) (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
    (((200 : ℝ) + (j.val : ℝ)) / 1600) ^ m * hpThetaJensenCellsBatch010Lower j.val *
        ((((200 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((200 : ℝ) + (j.val : ℝ)) / 1600)) ≤
      (∫ u : ℝ in Set.Ioo (((200 : ℝ) + (j.val : ℝ)) / 1600)
        (((200 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (((200 : ℝ) + (j.val : ℝ)) / 1600)
        (((200 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ≤
        (((200 : ℝ) + (j.val : ℝ) + 1) / 1600) ^ m * hpThetaJensenCellsBatch010Upper j.val *
          ((((200 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((200 : ℝ) + (j.val : ℝ)) / 1600)) := by
  apply hpThetaJensen_cellIntegral_bounds m hm
  · positivity
  · linarith
  · fin_cases j <;> norm_num [hpThetaJensenCellsBatch010Lower]
  · exact hpThetaJensenCellsBatch010_bounds j

theorem hpThetaJensenCellsBatch011_cellIntegral_bounds
    (j : Fin 20) (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
    (((220 : ℝ) + (j.val : ℝ)) / 1600) ^ m * hpThetaJensenCellsBatch011Lower j.val *
        ((((220 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((220 : ℝ) + (j.val : ℝ)) / 1600)) ≤
      (∫ u : ℝ in Set.Ioo (((220 : ℝ) + (j.val : ℝ)) / 1600)
        (((220 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (((220 : ℝ) + (j.val : ℝ)) / 1600)
        (((220 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ≤
        (((220 : ℝ) + (j.val : ℝ) + 1) / 1600) ^ m * hpThetaJensenCellsBatch011Upper j.val *
          ((((220 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((220 : ℝ) + (j.val : ℝ)) / 1600)) := by
  apply hpThetaJensen_cellIntegral_bounds m hm
  · positivity
  · linarith
  · fin_cases j <;> norm_num [hpThetaJensenCellsBatch011Lower]
  · exact hpThetaJensenCellsBatch011_bounds j

theorem hpThetaJensenCellsBatch012_cellIntegral_bounds
    (j : Fin 20) (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
    (((240 : ℝ) + (j.val : ℝ)) / 1600) ^ m * hpThetaJensenCellsBatch012Lower j.val *
        ((((240 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((240 : ℝ) + (j.val : ℝ)) / 1600)) ≤
      (∫ u : ℝ in Set.Ioo (((240 : ℝ) + (j.val : ℝ)) / 1600)
        (((240 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (((240 : ℝ) + (j.val : ℝ)) / 1600)
        (((240 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ≤
        (((240 : ℝ) + (j.val : ℝ) + 1) / 1600) ^ m * hpThetaJensenCellsBatch012Upper j.val *
          ((((240 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((240 : ℝ) + (j.val : ℝ)) / 1600)) := by
  apply hpThetaJensen_cellIntegral_bounds m hm
  · positivity
  · linarith
  · fin_cases j <;> norm_num [hpThetaJensenCellsBatch012Lower]
  · exact hpThetaJensenCellsBatch012_bounds j

theorem hpThetaJensenCellsBatch013_cellIntegral_bounds
    (j : Fin 20) (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
    (((260 : ℝ) + (j.val : ℝ)) / 1600) ^ m * hpThetaJensenCellsBatch013Lower j.val *
        ((((260 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((260 : ℝ) + (j.val : ℝ)) / 1600)) ≤
      (∫ u : ℝ in Set.Ioo (((260 : ℝ) + (j.val : ℝ)) / 1600)
        (((260 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (((260 : ℝ) + (j.val : ℝ)) / 1600)
        (((260 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ≤
        (((260 : ℝ) + (j.val : ℝ) + 1) / 1600) ^ m * hpThetaJensenCellsBatch013Upper j.val *
          ((((260 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((260 : ℝ) + (j.val : ℝ)) / 1600)) := by
  apply hpThetaJensen_cellIntegral_bounds m hm
  · positivity
  · linarith
  · fin_cases j <;> norm_num [hpThetaJensenCellsBatch013Lower]
  · exact hpThetaJensenCellsBatch013_bounds j

theorem hpThetaJensenCellsBatch014_cellIntegral_bounds
    (j : Fin 20) (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
    (((280 : ℝ) + (j.val : ℝ)) / 1600) ^ m * hpThetaJensenCellsBatch014Lower j.val *
        ((((280 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((280 : ℝ) + (j.val : ℝ)) / 1600)) ≤
      (∫ u : ℝ in Set.Ioo (((280 : ℝ) + (j.val : ℝ)) / 1600)
        (((280 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (((280 : ℝ) + (j.val : ℝ)) / 1600)
        (((280 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ≤
        (((280 : ℝ) + (j.val : ℝ) + 1) / 1600) ^ m * hpThetaJensenCellsBatch014Upper j.val *
          ((((280 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((280 : ℝ) + (j.val : ℝ)) / 1600)) := by
  apply hpThetaJensen_cellIntegral_bounds m hm
  · positivity
  · linarith
  · fin_cases j <;> norm_num [hpThetaJensenCellsBatch014Lower]
  · exact hpThetaJensenCellsBatch014_bounds j

theorem hpThetaJensenCellsBatch015_cellIntegral_bounds
    (j : Fin 20) (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
    (((300 : ℝ) + (j.val : ℝ)) / 1600) ^ m * hpThetaJensenCellsBatch015Lower j.val *
        ((((300 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((300 : ℝ) + (j.val : ℝ)) / 1600)) ≤
      (∫ u : ℝ in Set.Ioo (((300 : ℝ) + (j.val : ℝ)) / 1600)
        (((300 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (((300 : ℝ) + (j.val : ℝ)) / 1600)
        (((300 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ≤
        (((300 : ℝ) + (j.val : ℝ) + 1) / 1600) ^ m * hpThetaJensenCellsBatch015Upper j.val *
          ((((300 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((300 : ℝ) + (j.val : ℝ)) / 1600)) := by
  apply hpThetaJensen_cellIntegral_bounds m hm
  · positivity
  · linarith
  · fin_cases j <;> norm_num [hpThetaJensenCellsBatch015Lower]
  · exact hpThetaJensenCellsBatch015_bounds j

theorem hpThetaJensenCellsBatch016_cellIntegral_bounds
    (j : Fin 20) (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
    (((320 : ℝ) + (j.val : ℝ)) / 1600) ^ m * hpThetaJensenCellsBatch016Lower j.val *
        ((((320 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((320 : ℝ) + (j.val : ℝ)) / 1600)) ≤
      (∫ u : ℝ in Set.Ioo (((320 : ℝ) + (j.val : ℝ)) / 1600)
        (((320 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (((320 : ℝ) + (j.val : ℝ)) / 1600)
        (((320 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ≤
        (((320 : ℝ) + (j.val : ℝ) + 1) / 1600) ^ m * hpThetaJensenCellsBatch016Upper j.val *
          ((((320 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((320 : ℝ) + (j.val : ℝ)) / 1600)) := by
  apply hpThetaJensen_cellIntegral_bounds m hm
  · positivity
  · linarith
  · fin_cases j <;> norm_num [hpThetaJensenCellsBatch016Lower]
  · exact hpThetaJensenCellsBatch016_bounds j

theorem hpThetaJensenCellsBatch017_cellIntegral_bounds
    (j : Fin 20) (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
    (((340 : ℝ) + (j.val : ℝ)) / 1600) ^ m * hpThetaJensenCellsBatch017Lower j.val *
        ((((340 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((340 : ℝ) + (j.val : ℝ)) / 1600)) ≤
      (∫ u : ℝ in Set.Ioo (((340 : ℝ) + (j.val : ℝ)) / 1600)
        (((340 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (((340 : ℝ) + (j.val : ℝ)) / 1600)
        (((340 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ≤
        (((340 : ℝ) + (j.val : ℝ) + 1) / 1600) ^ m * hpThetaJensenCellsBatch017Upper j.val *
          ((((340 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((340 : ℝ) + (j.val : ℝ)) / 1600)) := by
  apply hpThetaJensen_cellIntegral_bounds m hm
  · positivity
  · linarith
  · fin_cases j <;> norm_num [hpThetaJensenCellsBatch017Lower]
  · exact hpThetaJensenCellsBatch017_bounds j

theorem hpThetaJensenCellsBatch018_cellIntegral_bounds
    (j : Fin 20) (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
    (((360 : ℝ) + (j.val : ℝ)) / 1600) ^ m * hpThetaJensenCellsBatch018Lower j.val *
        ((((360 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((360 : ℝ) + (j.val : ℝ)) / 1600)) ≤
      (∫ u : ℝ in Set.Ioo (((360 : ℝ) + (j.val : ℝ)) / 1600)
        (((360 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (((360 : ℝ) + (j.val : ℝ)) / 1600)
        (((360 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ≤
        (((360 : ℝ) + (j.val : ℝ) + 1) / 1600) ^ m * hpThetaJensenCellsBatch018Upper j.val *
          ((((360 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((360 : ℝ) + (j.val : ℝ)) / 1600)) := by
  apply hpThetaJensen_cellIntegral_bounds m hm
  · positivity
  · linarith
  · fin_cases j <;> norm_num [hpThetaJensenCellsBatch018Lower]
  · exact hpThetaJensenCellsBatch018_bounds j

theorem hpThetaJensenCellsBatch019_cellIntegral_bounds
    (j : Fin 20) (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
    (((380 : ℝ) + (j.val : ℝ)) / 1600) ^ m * hpThetaJensenCellsBatch019Lower j.val *
        ((((380 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((380 : ℝ) + (j.val : ℝ)) / 1600)) ≤
      (∫ u : ℝ in Set.Ioo (((380 : ℝ) + (j.val : ℝ)) / 1600)
        (((380 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (((380 : ℝ) + (j.val : ℝ)) / 1600)
        (((380 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ≤
        (((380 : ℝ) + (j.val : ℝ) + 1) / 1600) ^ m * hpThetaJensenCellsBatch019Upper j.val *
          ((((380 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((380 : ℝ) + (j.val : ℝ)) / 1600)) := by
  apply hpThetaJensen_cellIntegral_bounds m hm
  · positivity
  · linarith
  · fin_cases j <;> norm_num [hpThetaJensenCellsBatch019Lower]
  · exact hpThetaJensenCellsBatch019_bounds j

theorem hpThetaJensenCellsBatch020_cellIntegral_bounds
    (j : Fin 20) (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
    (((400 : ℝ) + (j.val : ℝ)) / 1600) ^ m * hpThetaJensenCellsBatch020Lower j.val *
        ((((400 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((400 : ℝ) + (j.val : ℝ)) / 1600)) ≤
      (∫ u : ℝ in Set.Ioo (((400 : ℝ) + (j.val : ℝ)) / 1600)
        (((400 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (((400 : ℝ) + (j.val : ℝ)) / 1600)
        (((400 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ≤
        (((400 : ℝ) + (j.val : ℝ) + 1) / 1600) ^ m * hpThetaJensenCellsBatch020Upper j.val *
          ((((400 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((400 : ℝ) + (j.val : ℝ)) / 1600)) := by
  apply hpThetaJensen_cellIntegral_bounds m hm
  · positivity
  · linarith
  · fin_cases j <;> norm_num [hpThetaJensenCellsBatch020Lower]
  · exact hpThetaJensenCellsBatch020_bounds j

theorem hpThetaJensenCellsBatch021_cellIntegral_bounds
    (j : Fin 20) (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
    (((420 : ℝ) + (j.val : ℝ)) / 1600) ^ m * hpThetaJensenCellsBatch021Lower j.val *
        ((((420 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((420 : ℝ) + (j.val : ℝ)) / 1600)) ≤
      (∫ u : ℝ in Set.Ioo (((420 : ℝ) + (j.val : ℝ)) / 1600)
        (((420 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (((420 : ℝ) + (j.val : ℝ)) / 1600)
        (((420 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ≤
        (((420 : ℝ) + (j.val : ℝ) + 1) / 1600) ^ m * hpThetaJensenCellsBatch021Upper j.val *
          ((((420 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((420 : ℝ) + (j.val : ℝ)) / 1600)) := by
  apply hpThetaJensen_cellIntegral_bounds m hm
  · positivity
  · linarith
  · fin_cases j <;> norm_num [hpThetaJensenCellsBatch021Lower]
  · exact hpThetaJensenCellsBatch021_bounds j

theorem hpThetaJensenCellsBatch022_cellIntegral_bounds
    (j : Fin 20) (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
    (((440 : ℝ) + (j.val : ℝ)) / 1600) ^ m * hpThetaJensenCellsBatch022Lower j.val *
        ((((440 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((440 : ℝ) + (j.val : ℝ)) / 1600)) ≤
      (∫ u : ℝ in Set.Ioo (((440 : ℝ) + (j.val : ℝ)) / 1600)
        (((440 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (((440 : ℝ) + (j.val : ℝ)) / 1600)
        (((440 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ≤
        (((440 : ℝ) + (j.val : ℝ) + 1) / 1600) ^ m * hpThetaJensenCellsBatch022Upper j.val *
          ((((440 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((440 : ℝ) + (j.val : ℝ)) / 1600)) := by
  apply hpThetaJensen_cellIntegral_bounds m hm
  · positivity
  · linarith
  · fin_cases j <;> norm_num [hpThetaJensenCellsBatch022Lower]
  · exact hpThetaJensenCellsBatch022_bounds j

theorem hpThetaJensenCellsBatch023_cellIntegral_bounds
    (j : Fin 20) (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
    (((460 : ℝ) + (j.val : ℝ)) / 1600) ^ m * hpThetaJensenCellsBatch023Lower j.val *
        ((((460 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((460 : ℝ) + (j.val : ℝ)) / 1600)) ≤
      (∫ u : ℝ in Set.Ioo (((460 : ℝ) + (j.val : ℝ)) / 1600)
        (((460 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (((460 : ℝ) + (j.val : ℝ)) / 1600)
        (((460 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ≤
        (((460 : ℝ) + (j.val : ℝ) + 1) / 1600) ^ m * hpThetaJensenCellsBatch023Upper j.val *
          ((((460 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((460 : ℝ) + (j.val : ℝ)) / 1600)) := by
  apply hpThetaJensen_cellIntegral_bounds m hm
  · positivity
  · linarith
  · fin_cases j <;> norm_num [hpThetaJensenCellsBatch023Lower]
  · exact hpThetaJensenCellsBatch023_bounds j

theorem hpThetaJensenCellsBatch024_cellIntegral_bounds
    (j : Fin 20) (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
    (((480 : ℝ) + (j.val : ℝ)) / 1600) ^ m * hpThetaJensenCellsBatch024Lower j.val *
        ((((480 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((480 : ℝ) + (j.val : ℝ)) / 1600)) ≤
      (∫ u : ℝ in Set.Ioo (((480 : ℝ) + (j.val : ℝ)) / 1600)
        (((480 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (((480 : ℝ) + (j.val : ℝ)) / 1600)
        (((480 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ≤
        (((480 : ℝ) + (j.val : ℝ) + 1) / 1600) ^ m * hpThetaJensenCellsBatch024Upper j.val *
          ((((480 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((480 : ℝ) + (j.val : ℝ)) / 1600)) := by
  apply hpThetaJensen_cellIntegral_bounds m hm
  · positivity
  · linarith
  · fin_cases j <;> norm_num [hpThetaJensenCellsBatch024Lower]
  · exact hpThetaJensenCellsBatch024_bounds j

theorem hpThetaJensenCellsBatch025_cellIntegral_bounds
    (j : Fin 20) (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
    (((500 : ℝ) + (j.val : ℝ)) / 1600) ^ m * hpThetaJensenCellsBatch025Lower j.val *
        ((((500 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((500 : ℝ) + (j.val : ℝ)) / 1600)) ≤
      (∫ u : ℝ in Set.Ioo (((500 : ℝ) + (j.val : ℝ)) / 1600)
        (((500 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (((500 : ℝ) + (j.val : ℝ)) / 1600)
        (((500 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ≤
        (((500 : ℝ) + (j.val : ℝ) + 1) / 1600) ^ m * hpThetaJensenCellsBatch025Upper j.val *
          ((((500 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((500 : ℝ) + (j.val : ℝ)) / 1600)) := by
  apply hpThetaJensen_cellIntegral_bounds m hm
  · positivity
  · linarith
  · fin_cases j <;> norm_num [hpThetaJensenCellsBatch025Lower]
  · exact hpThetaJensenCellsBatch025_bounds j

theorem hpThetaJensenCellsBatch026_cellIntegral_bounds
    (j : Fin 20) (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
    (((520 : ℝ) + (j.val : ℝ)) / 1600) ^ m * hpThetaJensenCellsBatch026Lower j.val *
        ((((520 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((520 : ℝ) + (j.val : ℝ)) / 1600)) ≤
      (∫ u : ℝ in Set.Ioo (((520 : ℝ) + (j.val : ℝ)) / 1600)
        (((520 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (((520 : ℝ) + (j.val : ℝ)) / 1600)
        (((520 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ≤
        (((520 : ℝ) + (j.val : ℝ) + 1) / 1600) ^ m * hpThetaJensenCellsBatch026Upper j.val *
          ((((520 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((520 : ℝ) + (j.val : ℝ)) / 1600)) := by
  apply hpThetaJensen_cellIntegral_bounds m hm
  · positivity
  · linarith
  · fin_cases j <;> norm_num [hpThetaJensenCellsBatch026Lower]
  · exact hpThetaJensenCellsBatch026_bounds j

theorem hpThetaJensenCellsBatch027_cellIntegral_bounds
    (j : Fin 20) (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
    (((540 : ℝ) + (j.val : ℝ)) / 1600) ^ m * hpThetaJensenCellsBatch027Lower j.val *
        ((((540 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((540 : ℝ) + (j.val : ℝ)) / 1600)) ≤
      (∫ u : ℝ in Set.Ioo (((540 : ℝ) + (j.val : ℝ)) / 1600)
        (((540 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (((540 : ℝ) + (j.val : ℝ)) / 1600)
        (((540 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ≤
        (((540 : ℝ) + (j.val : ℝ) + 1) / 1600) ^ m * hpThetaJensenCellsBatch027Upper j.val *
          ((((540 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((540 : ℝ) + (j.val : ℝ)) / 1600)) := by
  apply hpThetaJensen_cellIntegral_bounds m hm
  · positivity
  · linarith
  · fin_cases j <;> norm_num [hpThetaJensenCellsBatch027Lower]
  · exact hpThetaJensenCellsBatch027_bounds j

theorem hpThetaJensenCellsBatch028_cellIntegral_bounds
    (j : Fin 20) (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
    (((560 : ℝ) + (j.val : ℝ)) / 1600) ^ m * hpThetaJensenCellsBatch028Lower j.val *
        ((((560 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((560 : ℝ) + (j.val : ℝ)) / 1600)) ≤
      (∫ u : ℝ in Set.Ioo (((560 : ℝ) + (j.val : ℝ)) / 1600)
        (((560 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (((560 : ℝ) + (j.val : ℝ)) / 1600)
        (((560 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ≤
        (((560 : ℝ) + (j.val : ℝ) + 1) / 1600) ^ m * hpThetaJensenCellsBatch028Upper j.val *
          ((((560 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((560 : ℝ) + (j.val : ℝ)) / 1600)) := by
  apply hpThetaJensen_cellIntegral_bounds m hm
  · positivity
  · linarith
  · fin_cases j <;> norm_num [hpThetaJensenCellsBatch028Lower]
  · exact hpThetaJensenCellsBatch028_bounds j

theorem hpThetaJensenCellsBatch029_cellIntegral_bounds
    (j : Fin 20) (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
    (((580 : ℝ) + (j.val : ℝ)) / 1600) ^ m * hpThetaJensenCellsBatch029Lower j.val *
        ((((580 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((580 : ℝ) + (j.val : ℝ)) / 1600)) ≤
      (∫ u : ℝ in Set.Ioo (((580 : ℝ) + (j.val : ℝ)) / 1600)
        (((580 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (((580 : ℝ) + (j.val : ℝ)) / 1600)
        (((580 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ≤
        (((580 : ℝ) + (j.val : ℝ) + 1) / 1600) ^ m * hpThetaJensenCellsBatch029Upper j.val *
          ((((580 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((580 : ℝ) + (j.val : ℝ)) / 1600)) := by
  apply hpThetaJensen_cellIntegral_bounds m hm
  · positivity
  · linarith
  · fin_cases j <;> norm_num [hpThetaJensenCellsBatch029Lower]
  · exact hpThetaJensenCellsBatch029_bounds j

theorem hpThetaJensenCellsBatch030_cellIntegral_bounds
    (j : Fin 20) (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
    (((600 : ℝ) + (j.val : ℝ)) / 1600) ^ m * hpThetaJensenCellsBatch030Lower j.val *
        ((((600 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((600 : ℝ) + (j.val : ℝ)) / 1600)) ≤
      (∫ u : ℝ in Set.Ioo (((600 : ℝ) + (j.val : ℝ)) / 1600)
        (((600 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (((600 : ℝ) + (j.val : ℝ)) / 1600)
        (((600 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ≤
        (((600 : ℝ) + (j.val : ℝ) + 1) / 1600) ^ m * hpThetaJensenCellsBatch030Upper j.val *
          ((((600 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((600 : ℝ) + (j.val : ℝ)) / 1600)) := by
  apply hpThetaJensen_cellIntegral_bounds m hm
  · positivity
  · linarith
  · fin_cases j <;> norm_num [hpThetaJensenCellsBatch030Lower]
  · exact hpThetaJensenCellsBatch030_bounds j

theorem hpThetaJensenCellsBatch031_cellIntegral_bounds
    (j : Fin 20) (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
    (((620 : ℝ) + (j.val : ℝ)) / 1600) ^ m * hpThetaJensenCellsBatch031Lower j.val *
        ((((620 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((620 : ℝ) + (j.val : ℝ)) / 1600)) ≤
      (∫ u : ℝ in Set.Ioo (((620 : ℝ) + (j.val : ℝ)) / 1600)
        (((620 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (((620 : ℝ) + (j.val : ℝ)) / 1600)
        (((620 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ≤
        (((620 : ℝ) + (j.val : ℝ) + 1) / 1600) ^ m * hpThetaJensenCellsBatch031Upper j.val *
          ((((620 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((620 : ℝ) + (j.val : ℝ)) / 1600)) := by
  apply hpThetaJensen_cellIntegral_bounds m hm
  · positivity
  · linarith
  · fin_cases j <;> norm_num [hpThetaJensenCellsBatch031Lower]
  · exact hpThetaJensenCellsBatch031_bounds j

theorem hpThetaJensenCellsBatch032_cellIntegral_bounds
    (j : Fin 20) (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
    (((640 : ℝ) + (j.val : ℝ)) / 1600) ^ m * hpThetaJensenCellsBatch032Lower j.val *
        ((((640 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((640 : ℝ) + (j.val : ℝ)) / 1600)) ≤
      (∫ u : ℝ in Set.Ioo (((640 : ℝ) + (j.val : ℝ)) / 1600)
        (((640 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (((640 : ℝ) + (j.val : ℝ)) / 1600)
        (((640 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ≤
        (((640 : ℝ) + (j.val : ℝ) + 1) / 1600) ^ m * hpThetaJensenCellsBatch032Upper j.val *
          ((((640 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((640 : ℝ) + (j.val : ℝ)) / 1600)) := by
  apply hpThetaJensen_cellIntegral_bounds m hm
  · positivity
  · linarith
  · fin_cases j <;> norm_num [hpThetaJensenCellsBatch032Lower]
  · exact hpThetaJensenCellsBatch032_bounds j

theorem hpThetaJensenCellsBatch033_cellIntegral_bounds
    (j : Fin 20) (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
    (((660 : ℝ) + (j.val : ℝ)) / 1600) ^ m * hpThetaJensenCellsBatch033Lower j.val *
        ((((660 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((660 : ℝ) + (j.val : ℝ)) / 1600)) ≤
      (∫ u : ℝ in Set.Ioo (((660 : ℝ) + (j.val : ℝ)) / 1600)
        (((660 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (((660 : ℝ) + (j.val : ℝ)) / 1600)
        (((660 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ≤
        (((660 : ℝ) + (j.val : ℝ) + 1) / 1600) ^ m * hpThetaJensenCellsBatch033Upper j.val *
          ((((660 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((660 : ℝ) + (j.val : ℝ)) / 1600)) := by
  apply hpThetaJensen_cellIntegral_bounds m hm
  · positivity
  · linarith
  · fin_cases j <;> norm_num [hpThetaJensenCellsBatch033Lower]
  · exact hpThetaJensenCellsBatch033_bounds j

theorem hpThetaJensenCellsBatch034_cellIntegral_bounds
    (j : Fin 20) (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
    (((680 : ℝ) + (j.val : ℝ)) / 1600) ^ m * hpThetaJensenCellsBatch034Lower j.val *
        ((((680 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((680 : ℝ) + (j.val : ℝ)) / 1600)) ≤
      (∫ u : ℝ in Set.Ioo (((680 : ℝ) + (j.val : ℝ)) / 1600)
        (((680 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (((680 : ℝ) + (j.val : ℝ)) / 1600)
        (((680 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ≤
        (((680 : ℝ) + (j.val : ℝ) + 1) / 1600) ^ m * hpThetaJensenCellsBatch034Upper j.val *
          ((((680 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((680 : ℝ) + (j.val : ℝ)) / 1600)) := by
  apply hpThetaJensen_cellIntegral_bounds m hm
  · positivity
  · linarith
  · fin_cases j <;> norm_num [hpThetaJensenCellsBatch034Lower]
  · exact hpThetaJensenCellsBatch034_bounds j

theorem hpThetaJensenCellsBatch035_cellIntegral_bounds
    (j : Fin 20) (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
    (((700 : ℝ) + (j.val : ℝ)) / 1600) ^ m * hpThetaJensenCellsBatch035Lower j.val *
        ((((700 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((700 : ℝ) + (j.val : ℝ)) / 1600)) ≤
      (∫ u : ℝ in Set.Ioo (((700 : ℝ) + (j.val : ℝ)) / 1600)
        (((700 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (((700 : ℝ) + (j.val : ℝ)) / 1600)
        (((700 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ≤
        (((700 : ℝ) + (j.val : ℝ) + 1) / 1600) ^ m * hpThetaJensenCellsBatch035Upper j.val *
          ((((700 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((700 : ℝ) + (j.val : ℝ)) / 1600)) := by
  apply hpThetaJensen_cellIntegral_bounds m hm
  · positivity
  · linarith
  · fin_cases j <;> norm_num [hpThetaJensenCellsBatch035Lower]
  · exact hpThetaJensenCellsBatch035_bounds j

theorem hpThetaJensenCellsBatch036_cellIntegral_bounds
    (j : Fin 20) (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
    (((720 : ℝ) + (j.val : ℝ)) / 1600) ^ m * hpThetaJensenCellsBatch036Lower j.val *
        ((((720 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((720 : ℝ) + (j.val : ℝ)) / 1600)) ≤
      (∫ u : ℝ in Set.Ioo (((720 : ℝ) + (j.val : ℝ)) / 1600)
        (((720 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (((720 : ℝ) + (j.val : ℝ)) / 1600)
        (((720 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ≤
        (((720 : ℝ) + (j.val : ℝ) + 1) / 1600) ^ m * hpThetaJensenCellsBatch036Upper j.val *
          ((((720 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((720 : ℝ) + (j.val : ℝ)) / 1600)) := by
  apply hpThetaJensen_cellIntegral_bounds m hm
  · positivity
  · linarith
  · fin_cases j <;> norm_num [hpThetaJensenCellsBatch036Lower]
  · exact hpThetaJensenCellsBatch036_bounds j

theorem hpThetaJensenCellsBatch037_cellIntegral_bounds
    (j : Fin 20) (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
    (((740 : ℝ) + (j.val : ℝ)) / 1600) ^ m * hpThetaJensenCellsBatch037Lower j.val *
        ((((740 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((740 : ℝ) + (j.val : ℝ)) / 1600)) ≤
      (∫ u : ℝ in Set.Ioo (((740 : ℝ) + (j.val : ℝ)) / 1600)
        (((740 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (((740 : ℝ) + (j.val : ℝ)) / 1600)
        (((740 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ≤
        (((740 : ℝ) + (j.val : ℝ) + 1) / 1600) ^ m * hpThetaJensenCellsBatch037Upper j.val *
          ((((740 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((740 : ℝ) + (j.val : ℝ)) / 1600)) := by
  apply hpThetaJensen_cellIntegral_bounds m hm
  · positivity
  · linarith
  · fin_cases j <;> norm_num [hpThetaJensenCellsBatch037Lower]
  · exact hpThetaJensenCellsBatch037_bounds j

theorem hpThetaJensenCellsBatch038_cellIntegral_bounds
    (j : Fin 20) (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
    (((760 : ℝ) + (j.val : ℝ)) / 1600) ^ m * hpThetaJensenCellsBatch038Lower j.val *
        ((((760 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((760 : ℝ) + (j.val : ℝ)) / 1600)) ≤
      (∫ u : ℝ in Set.Ioo (((760 : ℝ) + (j.val : ℝ)) / 1600)
        (((760 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (((760 : ℝ) + (j.val : ℝ)) / 1600)
        (((760 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ≤
        (((760 : ℝ) + (j.val : ℝ) + 1) / 1600) ^ m * hpThetaJensenCellsBatch038Upper j.val *
          ((((760 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((760 : ℝ) + (j.val : ℝ)) / 1600)) := by
  apply hpThetaJensen_cellIntegral_bounds m hm
  · positivity
  · linarith
  · fin_cases j <;> norm_num [hpThetaJensenCellsBatch038Lower]
  · exact hpThetaJensenCellsBatch038_bounds j

theorem hpThetaJensenCellsBatch039_cellIntegral_bounds
    (j : Fin 20) (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
    (((780 : ℝ) + (j.val : ℝ)) / 1600) ^ m * hpThetaJensenCellsBatch039Lower j.val *
        ((((780 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((780 : ℝ) + (j.val : ℝ)) / 1600)) ≤
      (∫ u : ℝ in Set.Ioo (((780 : ℝ) + (j.val : ℝ)) / 1600)
        (((780 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (((780 : ℝ) + (j.val : ℝ)) / 1600)
        (((780 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ≤
        (((780 : ℝ) + (j.val : ℝ) + 1) / 1600) ^ m * hpThetaJensenCellsBatch039Upper j.val *
          ((((780 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((780 : ℝ) + (j.val : ℝ)) / 1600)) := by
  apply hpThetaJensen_cellIntegral_bounds m hm
  · positivity
  · linarith
  · fin_cases j <;> norm_num [hpThetaJensenCellsBatch039Lower]
  · exact hpThetaJensenCellsBatch039_bounds j

theorem hpThetaJensenCellsBatch040_cellIntegral_bounds
    (j : Fin 20) (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
    (((800 : ℝ) + (j.val : ℝ)) / 1600) ^ m * hpThetaJensenCellsBatch040Lower j.val *
        ((((800 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((800 : ℝ) + (j.val : ℝ)) / 1600)) ≤
      (∫ u : ℝ in Set.Ioo (((800 : ℝ) + (j.val : ℝ)) / 1600)
        (((800 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (((800 : ℝ) + (j.val : ℝ)) / 1600)
        (((800 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ≤
        (((800 : ℝ) + (j.val : ℝ) + 1) / 1600) ^ m * hpThetaJensenCellsBatch040Upper j.val *
          ((((800 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((800 : ℝ) + (j.val : ℝ)) / 1600)) := by
  apply hpThetaJensen_cellIntegral_bounds m hm
  · positivity
  · linarith
  · fin_cases j <;> norm_num [hpThetaJensenCellsBatch040Lower]
  · exact hpThetaJensenCellsBatch040_bounds j

theorem hpThetaJensenCellsBatch041_cellIntegral_bounds
    (j : Fin 20) (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
    (((820 : ℝ) + (j.val : ℝ)) / 1600) ^ m * hpThetaJensenCellsBatch041Lower j.val *
        ((((820 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((820 : ℝ) + (j.val : ℝ)) / 1600)) ≤
      (∫ u : ℝ in Set.Ioo (((820 : ℝ) + (j.val : ℝ)) / 1600)
        (((820 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (((820 : ℝ) + (j.val : ℝ)) / 1600)
        (((820 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ≤
        (((820 : ℝ) + (j.val : ℝ) + 1) / 1600) ^ m * hpThetaJensenCellsBatch041Upper j.val *
          ((((820 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((820 : ℝ) + (j.val : ℝ)) / 1600)) := by
  apply hpThetaJensen_cellIntegral_bounds m hm
  · positivity
  · linarith
  · fin_cases j <;> norm_num [hpThetaJensenCellsBatch041Lower]
  · exact hpThetaJensenCellsBatch041_bounds j

theorem hpThetaJensenCellsBatch042_cellIntegral_bounds
    (j : Fin 20) (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
    (((840 : ℝ) + (j.val : ℝ)) / 1600) ^ m * hpThetaJensenCellsBatch042Lower j.val *
        ((((840 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((840 : ℝ) + (j.val : ℝ)) / 1600)) ≤
      (∫ u : ℝ in Set.Ioo (((840 : ℝ) + (j.val : ℝ)) / 1600)
        (((840 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (((840 : ℝ) + (j.val : ℝ)) / 1600)
        (((840 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ≤
        (((840 : ℝ) + (j.val : ℝ) + 1) / 1600) ^ m * hpThetaJensenCellsBatch042Upper j.val *
          ((((840 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((840 : ℝ) + (j.val : ℝ)) / 1600)) := by
  apply hpThetaJensen_cellIntegral_bounds m hm
  · positivity
  · linarith
  · fin_cases j <;> norm_num [hpThetaJensenCellsBatch042Lower]
  · exact hpThetaJensenCellsBatch042_bounds j

theorem hpThetaJensenCellsBatch043_cellIntegral_bounds
    (j : Fin 20) (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
    (((860 : ℝ) + (j.val : ℝ)) / 1600) ^ m * hpThetaJensenCellsBatch043Lower j.val *
        ((((860 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((860 : ℝ) + (j.val : ℝ)) / 1600)) ≤
      (∫ u : ℝ in Set.Ioo (((860 : ℝ) + (j.val : ℝ)) / 1600)
        (((860 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (((860 : ℝ) + (j.val : ℝ)) / 1600)
        (((860 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ≤
        (((860 : ℝ) + (j.val : ℝ) + 1) / 1600) ^ m * hpThetaJensenCellsBatch043Upper j.val *
          ((((860 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((860 : ℝ) + (j.val : ℝ)) / 1600)) := by
  apply hpThetaJensen_cellIntegral_bounds m hm
  · positivity
  · linarith
  · fin_cases j <;> norm_num [hpThetaJensenCellsBatch043Lower]
  · exact hpThetaJensenCellsBatch043_bounds j

theorem hpThetaJensenCellsBatch044_cellIntegral_bounds
    (j : Fin 20) (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
    (((880 : ℝ) + (j.val : ℝ)) / 1600) ^ m * hpThetaJensenCellsBatch044Lower j.val *
        ((((880 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((880 : ℝ) + (j.val : ℝ)) / 1600)) ≤
      (∫ u : ℝ in Set.Ioo (((880 : ℝ) + (j.val : ℝ)) / 1600)
        (((880 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (((880 : ℝ) + (j.val : ℝ)) / 1600)
        (((880 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ≤
        (((880 : ℝ) + (j.val : ℝ) + 1) / 1600) ^ m * hpThetaJensenCellsBatch044Upper j.val *
          ((((880 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((880 : ℝ) + (j.val : ℝ)) / 1600)) := by
  apply hpThetaJensen_cellIntegral_bounds m hm
  · positivity
  · linarith
  · fin_cases j <;> norm_num [hpThetaJensenCellsBatch044Lower]
  · exact hpThetaJensenCellsBatch044_bounds j

theorem hpThetaJensenCellsBatch045_cellIntegral_bounds
    (j : Fin 20) (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
    (((900 : ℝ) + (j.val : ℝ)) / 1600) ^ m * hpThetaJensenCellsBatch045Lower j.val *
        ((((900 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((900 : ℝ) + (j.val : ℝ)) / 1600)) ≤
      (∫ u : ℝ in Set.Ioo (((900 : ℝ) + (j.val : ℝ)) / 1600)
        (((900 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (((900 : ℝ) + (j.val : ℝ)) / 1600)
        (((900 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ≤
        (((900 : ℝ) + (j.val : ℝ) + 1) / 1600) ^ m * hpThetaJensenCellsBatch045Upper j.val *
          ((((900 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((900 : ℝ) + (j.val : ℝ)) / 1600)) := by
  apply hpThetaJensen_cellIntegral_bounds m hm
  · positivity
  · linarith
  · fin_cases j <;> norm_num [hpThetaJensenCellsBatch045Lower]
  · exact hpThetaJensenCellsBatch045_bounds j

theorem hpThetaJensenCellsBatch046_cellIntegral_bounds
    (j : Fin 20) (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
    (((920 : ℝ) + (j.val : ℝ)) / 1600) ^ m * hpThetaJensenCellsBatch046Lower j.val *
        ((((920 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((920 : ℝ) + (j.val : ℝ)) / 1600)) ≤
      (∫ u : ℝ in Set.Ioo (((920 : ℝ) + (j.val : ℝ)) / 1600)
        (((920 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (((920 : ℝ) + (j.val : ℝ)) / 1600)
        (((920 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ≤
        (((920 : ℝ) + (j.val : ℝ) + 1) / 1600) ^ m * hpThetaJensenCellsBatch046Upper j.val *
          ((((920 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((920 : ℝ) + (j.val : ℝ)) / 1600)) := by
  apply hpThetaJensen_cellIntegral_bounds m hm
  · positivity
  · linarith
  · fin_cases j <;> norm_num [hpThetaJensenCellsBatch046Lower]
  · exact hpThetaJensenCellsBatch046_bounds j

theorem hpThetaJensenCellsBatch047_cellIntegral_bounds
    (j : Fin 20) (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
    (((940 : ℝ) + (j.val : ℝ)) / 1600) ^ m * hpThetaJensenCellsBatch047Lower j.val *
        ((((940 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((940 : ℝ) + (j.val : ℝ)) / 1600)) ≤
      (∫ u : ℝ in Set.Ioo (((940 : ℝ) + (j.val : ℝ)) / 1600)
        (((940 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (((940 : ℝ) + (j.val : ℝ)) / 1600)
        (((940 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ≤
        (((940 : ℝ) + (j.val : ℝ) + 1) / 1600) ^ m * hpThetaJensenCellsBatch047Upper j.val *
          ((((940 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((940 : ℝ) + (j.val : ℝ)) / 1600)) := by
  apply hpThetaJensen_cellIntegral_bounds m hm
  · positivity
  · linarith
  · fin_cases j <;> norm_num [hpThetaJensenCellsBatch047Lower]
  · exact hpThetaJensenCellsBatch047_bounds j

theorem hpThetaJensenCellsBatch048_cellIntegral_bounds
    (j : Fin 20) (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
    (((960 : ℝ) + (j.val : ℝ)) / 1600) ^ m * hpThetaJensenCellsBatch048Lower j.val *
        ((((960 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((960 : ℝ) + (j.val : ℝ)) / 1600)) ≤
      (∫ u : ℝ in Set.Ioo (((960 : ℝ) + (j.val : ℝ)) / 1600)
        (((960 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (((960 : ℝ) + (j.val : ℝ)) / 1600)
        (((960 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ≤
        (((960 : ℝ) + (j.val : ℝ) + 1) / 1600) ^ m * hpThetaJensenCellsBatch048Upper j.val *
          ((((960 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((960 : ℝ) + (j.val : ℝ)) / 1600)) := by
  apply hpThetaJensen_cellIntegral_bounds m hm
  · positivity
  · linarith
  · fin_cases j <;> norm_num [hpThetaJensenCellsBatch048Lower]
  · exact hpThetaJensenCellsBatch048_bounds j

theorem hpThetaJensenCellsBatch049_cellIntegral_bounds
    (j : Fin 20) (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
    (((980 : ℝ) + (j.val : ℝ)) / 1600) ^ m * hpThetaJensenCellsBatch049Lower j.val *
        ((((980 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((980 : ℝ) + (j.val : ℝ)) / 1600)) ≤
      (∫ u : ℝ in Set.Ioo (((980 : ℝ) + (j.val : ℝ)) / 1600)
        (((980 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (((980 : ℝ) + (j.val : ℝ)) / 1600)
        (((980 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ≤
        (((980 : ℝ) + (j.val : ℝ) + 1) / 1600) ^ m * hpThetaJensenCellsBatch049Upper j.val *
          ((((980 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((980 : ℝ) + (j.val : ℝ)) / 1600)) := by
  apply hpThetaJensen_cellIntegral_bounds m hm
  · positivity
  · linarith
  · fin_cases j <;> norm_num [hpThetaJensenCellsBatch049Lower]
  · exact hpThetaJensenCellsBatch049_bounds j

theorem hpThetaJensenCellsBatch050_cellIntegral_bounds
    (j : Fin 20) (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
    (((1000 : ℝ) + (j.val : ℝ)) / 1600) ^ m * hpThetaJensenCellsBatch050Lower j.val *
        ((((1000 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((1000 : ℝ) + (j.val : ℝ)) / 1600)) ≤
      (∫ u : ℝ in Set.Ioo (((1000 : ℝ) + (j.val : ℝ)) / 1600)
        (((1000 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (((1000 : ℝ) + (j.val : ℝ)) / 1600)
        (((1000 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ≤
        (((1000 : ℝ) + (j.val : ℝ) + 1) / 1600) ^ m * hpThetaJensenCellsBatch050Upper j.val *
          ((((1000 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((1000 : ℝ) + (j.val : ℝ)) / 1600)) := by
  apply hpThetaJensen_cellIntegral_bounds m hm
  · positivity
  · linarith
  · fin_cases j <;> norm_num [hpThetaJensenCellsBatch050Lower]
  · exact hpThetaJensenCellsBatch050_bounds j

theorem hpThetaJensenCellsBatch051_cellIntegral_bounds
    (j : Fin 20) (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
    (((1020 : ℝ) + (j.val : ℝ)) / 1600) ^ m * hpThetaJensenCellsBatch051Lower j.val *
        ((((1020 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((1020 : ℝ) + (j.val : ℝ)) / 1600)) ≤
      (∫ u : ℝ in Set.Ioo (((1020 : ℝ) + (j.val : ℝ)) / 1600)
        (((1020 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (((1020 : ℝ) + (j.val : ℝ)) / 1600)
        (((1020 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ≤
        (((1020 : ℝ) + (j.val : ℝ) + 1) / 1600) ^ m * hpThetaJensenCellsBatch051Upper j.val *
          ((((1020 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((1020 : ℝ) + (j.val : ℝ)) / 1600)) := by
  apply hpThetaJensen_cellIntegral_bounds m hm
  · positivity
  · linarith
  · fin_cases j <;> norm_num [hpThetaJensenCellsBatch051Lower]
  · exact hpThetaJensenCellsBatch051_bounds j

theorem hpThetaJensenCellsBatch052_cellIntegral_bounds
    (j : Fin 20) (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
    (((1040 : ℝ) + (j.val : ℝ)) / 1600) ^ m * hpThetaJensenCellsBatch052Lower j.val *
        ((((1040 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((1040 : ℝ) + (j.val : ℝ)) / 1600)) ≤
      (∫ u : ℝ in Set.Ioo (((1040 : ℝ) + (j.val : ℝ)) / 1600)
        (((1040 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (((1040 : ℝ) + (j.val : ℝ)) / 1600)
        (((1040 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ≤
        (((1040 : ℝ) + (j.val : ℝ) + 1) / 1600) ^ m * hpThetaJensenCellsBatch052Upper j.val *
          ((((1040 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((1040 : ℝ) + (j.val : ℝ)) / 1600)) := by
  apply hpThetaJensen_cellIntegral_bounds m hm
  · positivity
  · linarith
  · fin_cases j <;> norm_num [hpThetaJensenCellsBatch052Lower]
  · exact hpThetaJensenCellsBatch052_bounds j

theorem hpThetaJensenCellsBatch053_cellIntegral_bounds
    (j : Fin 20) (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
    (((1060 : ℝ) + (j.val : ℝ)) / 1600) ^ m * hpThetaJensenCellsBatch053Lower j.val *
        ((((1060 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((1060 : ℝ) + (j.val : ℝ)) / 1600)) ≤
      (∫ u : ℝ in Set.Ioo (((1060 : ℝ) + (j.val : ℝ)) / 1600)
        (((1060 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (((1060 : ℝ) + (j.val : ℝ)) / 1600)
        (((1060 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ≤
        (((1060 : ℝ) + (j.val : ℝ) + 1) / 1600) ^ m * hpThetaJensenCellsBatch053Upper j.val *
          ((((1060 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((1060 : ℝ) + (j.val : ℝ)) / 1600)) := by
  apply hpThetaJensen_cellIntegral_bounds m hm
  · positivity
  · linarith
  · fin_cases j <;> norm_num [hpThetaJensenCellsBatch053Lower]
  · exact hpThetaJensenCellsBatch053_bounds j

theorem hpThetaJensenCellsBatch054_cellIntegral_bounds
    (j : Fin 20) (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
    (((1080 : ℝ) + (j.val : ℝ)) / 1600) ^ m * hpThetaJensenCellsBatch054Lower j.val *
        ((((1080 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((1080 : ℝ) + (j.val : ℝ)) / 1600)) ≤
      (∫ u : ℝ in Set.Ioo (((1080 : ℝ) + (j.val : ℝ)) / 1600)
        (((1080 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (((1080 : ℝ) + (j.val : ℝ)) / 1600)
        (((1080 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ≤
        (((1080 : ℝ) + (j.val : ℝ) + 1) / 1600) ^ m * hpThetaJensenCellsBatch054Upper j.val *
          ((((1080 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((1080 : ℝ) + (j.val : ℝ)) / 1600)) := by
  apply hpThetaJensen_cellIntegral_bounds m hm
  · positivity
  · linarith
  · fin_cases j <;> norm_num [hpThetaJensenCellsBatch054Lower]
  · exact hpThetaJensenCellsBatch054_bounds j

theorem hpThetaJensenCellsBatch055_cellIntegral_bounds
    (j : Fin 20) (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
    (((1100 : ℝ) + (j.val : ℝ)) / 1600) ^ m * hpThetaJensenCellsBatch055Lower j.val *
        ((((1100 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((1100 : ℝ) + (j.val : ℝ)) / 1600)) ≤
      (∫ u : ℝ in Set.Ioo (((1100 : ℝ) + (j.val : ℝ)) / 1600)
        (((1100 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (((1100 : ℝ) + (j.val : ℝ)) / 1600)
        (((1100 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ≤
        (((1100 : ℝ) + (j.val : ℝ) + 1) / 1600) ^ m * hpThetaJensenCellsBatch055Upper j.val *
          ((((1100 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((1100 : ℝ) + (j.val : ℝ)) / 1600)) := by
  apply hpThetaJensen_cellIntegral_bounds m hm
  · positivity
  · linarith
  · fin_cases j <;> norm_num [hpThetaJensenCellsBatch055Lower]
  · exact hpThetaJensenCellsBatch055_bounds j

theorem hpThetaJensenCellsBatch056_cellIntegral_bounds
    (j : Fin 20) (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
    (((1120 : ℝ) + (j.val : ℝ)) / 1600) ^ m * hpThetaJensenCellsBatch056Lower j.val *
        ((((1120 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((1120 : ℝ) + (j.val : ℝ)) / 1600)) ≤
      (∫ u : ℝ in Set.Ioo (((1120 : ℝ) + (j.val : ℝ)) / 1600)
        (((1120 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (((1120 : ℝ) + (j.val : ℝ)) / 1600)
        (((1120 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ≤
        (((1120 : ℝ) + (j.val : ℝ) + 1) / 1600) ^ m * hpThetaJensenCellsBatch056Upper j.val *
          ((((1120 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((1120 : ℝ) + (j.val : ℝ)) / 1600)) := by
  apply hpThetaJensen_cellIntegral_bounds m hm
  · positivity
  · linarith
  · fin_cases j <;> norm_num [hpThetaJensenCellsBatch056Lower]
  · exact hpThetaJensenCellsBatch056_bounds j

theorem hpThetaJensenCellsBatch057_cellIntegral_bounds
    (j : Fin 20) (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
    (((1140 : ℝ) + (j.val : ℝ)) / 1600) ^ m * hpThetaJensenCellsBatch057Lower j.val *
        ((((1140 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((1140 : ℝ) + (j.val : ℝ)) / 1600)) ≤
      (∫ u : ℝ in Set.Ioo (((1140 : ℝ) + (j.val : ℝ)) / 1600)
        (((1140 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (((1140 : ℝ) + (j.val : ℝ)) / 1600)
        (((1140 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ≤
        (((1140 : ℝ) + (j.val : ℝ) + 1) / 1600) ^ m * hpThetaJensenCellsBatch057Upper j.val *
          ((((1140 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((1140 : ℝ) + (j.val : ℝ)) / 1600)) := by
  apply hpThetaJensen_cellIntegral_bounds m hm
  · positivity
  · linarith
  · fin_cases j <;> norm_num [hpThetaJensenCellsBatch057Lower]
  · exact hpThetaJensenCellsBatch057_bounds j

theorem hpThetaJensenCellsBatch058_cellIntegral_bounds
    (j : Fin 20) (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
    (((1160 : ℝ) + (j.val : ℝ)) / 1600) ^ m * hpThetaJensenCellsBatch058Lower j.val *
        ((((1160 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((1160 : ℝ) + (j.val : ℝ)) / 1600)) ≤
      (∫ u : ℝ in Set.Ioo (((1160 : ℝ) + (j.val : ℝ)) / 1600)
        (((1160 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (((1160 : ℝ) + (j.val : ℝ)) / 1600)
        (((1160 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ≤
        (((1160 : ℝ) + (j.val : ℝ) + 1) / 1600) ^ m * hpThetaJensenCellsBatch058Upper j.val *
          ((((1160 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((1160 : ℝ) + (j.val : ℝ)) / 1600)) := by
  apply hpThetaJensen_cellIntegral_bounds m hm
  · positivity
  · linarith
  · fin_cases j <;> norm_num [hpThetaJensenCellsBatch058Lower]
  · exact hpThetaJensenCellsBatch058_bounds j

theorem hpThetaJensenCellsBatch059_cellIntegral_bounds
    (j : Fin 20) (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
    (((1180 : ℝ) + (j.val : ℝ)) / 1600) ^ m * hpThetaJensenCellsBatch059Lower j.val *
        ((((1180 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((1180 : ℝ) + (j.val : ℝ)) / 1600)) ≤
      (∫ u : ℝ in Set.Ioo (((1180 : ℝ) + (j.val : ℝ)) / 1600)
        (((1180 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (((1180 : ℝ) + (j.val : ℝ)) / 1600)
        (((1180 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ≤
        (((1180 : ℝ) + (j.val : ℝ) + 1) / 1600) ^ m * hpThetaJensenCellsBatch059Upper j.val *
          ((((1180 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((1180 : ℝ) + (j.val : ℝ)) / 1600)) := by
  apply hpThetaJensen_cellIntegral_bounds m hm
  · positivity
  · linarith
  · fin_cases j <;> norm_num [hpThetaJensenCellsBatch059Lower]
  · exact hpThetaJensenCellsBatch059_bounds j

theorem hpThetaJensenCellsBatch060_cellIntegral_bounds
    (j : Fin 20) (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
    (((1200 : ℝ) + (j.val : ℝ)) / 1600) ^ m * hpThetaJensenCellsBatch060Lower j.val *
        ((((1200 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((1200 : ℝ) + (j.val : ℝ)) / 1600)) ≤
      (∫ u : ℝ in Set.Ioo (((1200 : ℝ) + (j.val : ℝ)) / 1600)
        (((1200 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (((1200 : ℝ) + (j.val : ℝ)) / 1600)
        (((1200 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ≤
        (((1200 : ℝ) + (j.val : ℝ) + 1) / 1600) ^ m * hpThetaJensenCellsBatch060Upper j.val *
          ((((1200 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((1200 : ℝ) + (j.val : ℝ)) / 1600)) := by
  apply hpThetaJensen_cellIntegral_bounds m hm
  · positivity
  · linarith
  · fin_cases j <;> norm_num [hpThetaJensenCellsBatch060Lower]
  · exact hpThetaJensenCellsBatch060_bounds j

theorem hpThetaJensenCellsBatch061_cellIntegral_bounds
    (j : Fin 20) (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
    (((1220 : ℝ) + (j.val : ℝ)) / 1600) ^ m * hpThetaJensenCellsBatch061Lower j.val *
        ((((1220 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((1220 : ℝ) + (j.val : ℝ)) / 1600)) ≤
      (∫ u : ℝ in Set.Ioo (((1220 : ℝ) + (j.val : ℝ)) / 1600)
        (((1220 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (((1220 : ℝ) + (j.val : ℝ)) / 1600)
        (((1220 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ≤
        (((1220 : ℝ) + (j.val : ℝ) + 1) / 1600) ^ m * hpThetaJensenCellsBatch061Upper j.val *
          ((((1220 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((1220 : ℝ) + (j.val : ℝ)) / 1600)) := by
  apply hpThetaJensen_cellIntegral_bounds m hm
  · positivity
  · linarith
  · fin_cases j <;> norm_num [hpThetaJensenCellsBatch061Lower]
  · exact hpThetaJensenCellsBatch061_bounds j

theorem hpThetaJensenCellsBatch062_cellIntegral_bounds
    (j : Fin 20) (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
    (((1240 : ℝ) + (j.val : ℝ)) / 1600) ^ m * hpThetaJensenCellsBatch062Lower j.val *
        ((((1240 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((1240 : ℝ) + (j.val : ℝ)) / 1600)) ≤
      (∫ u : ℝ in Set.Ioo (((1240 : ℝ) + (j.val : ℝ)) / 1600)
        (((1240 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (((1240 : ℝ) + (j.val : ℝ)) / 1600)
        (((1240 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ≤
        (((1240 : ℝ) + (j.val : ℝ) + 1) / 1600) ^ m * hpThetaJensenCellsBatch062Upper j.val *
          ((((1240 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((1240 : ℝ) + (j.val : ℝ)) / 1600)) := by
  apply hpThetaJensen_cellIntegral_bounds m hm
  · positivity
  · linarith
  · fin_cases j <;> norm_num [hpThetaJensenCellsBatch062Lower]
  · exact hpThetaJensenCellsBatch062_bounds j

theorem hpThetaJensenCellsBatch063_cellIntegral_bounds
    (j : Fin 20) (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
    (((1260 : ℝ) + (j.val : ℝ)) / 1600) ^ m * hpThetaJensenCellsBatch063Lower j.val *
        ((((1260 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((1260 : ℝ) + (j.val : ℝ)) / 1600)) ≤
      (∫ u : ℝ in Set.Ioo (((1260 : ℝ) + (j.val : ℝ)) / 1600)
        (((1260 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (((1260 : ℝ) + (j.val : ℝ)) / 1600)
        (((1260 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ≤
        (((1260 : ℝ) + (j.val : ℝ) + 1) / 1600) ^ m * hpThetaJensenCellsBatch063Upper j.val *
          ((((1260 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((1260 : ℝ) + (j.val : ℝ)) / 1600)) := by
  apply hpThetaJensen_cellIntegral_bounds m hm
  · positivity
  · linarith
  · fin_cases j <;> norm_num [hpThetaJensenCellsBatch063Lower]
  · exact hpThetaJensenCellsBatch063_bounds j

theorem hpThetaJensenCellsBatch064_cellIntegral_bounds
    (j : Fin 20) (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
    (((1280 : ℝ) + (j.val : ℝ)) / 1600) ^ m * hpThetaJensenCellsBatch064Lower j.val *
        ((((1280 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((1280 : ℝ) + (j.val : ℝ)) / 1600)) ≤
      (∫ u : ℝ in Set.Ioo (((1280 : ℝ) + (j.val : ℝ)) / 1600)
        (((1280 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (((1280 : ℝ) + (j.val : ℝ)) / 1600)
        (((1280 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ≤
        (((1280 : ℝ) + (j.val : ℝ) + 1) / 1600) ^ m * hpThetaJensenCellsBatch064Upper j.val *
          ((((1280 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((1280 : ℝ) + (j.val : ℝ)) / 1600)) := by
  apply hpThetaJensen_cellIntegral_bounds m hm
  · positivity
  · linarith
  · fin_cases j <;> norm_num [hpThetaJensenCellsBatch064Lower]
  · exact hpThetaJensenCellsBatch064_bounds j

theorem hpThetaJensenCellsBatch065_cellIntegral_bounds
    (j : Fin 20) (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
    (((1300 : ℝ) + (j.val : ℝ)) / 1600) ^ m * hpThetaJensenCellsBatch065Lower j.val *
        ((((1300 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((1300 : ℝ) + (j.val : ℝ)) / 1600)) ≤
      (∫ u : ℝ in Set.Ioo (((1300 : ℝ) + (j.val : ℝ)) / 1600)
        (((1300 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (((1300 : ℝ) + (j.val : ℝ)) / 1600)
        (((1300 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ≤
        (((1300 : ℝ) + (j.val : ℝ) + 1) / 1600) ^ m * hpThetaJensenCellsBatch065Upper j.val *
          ((((1300 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((1300 : ℝ) + (j.val : ℝ)) / 1600)) := by
  apply hpThetaJensen_cellIntegral_bounds m hm
  · positivity
  · linarith
  · fin_cases j <;> norm_num [hpThetaJensenCellsBatch065Lower]
  · exact hpThetaJensenCellsBatch065_bounds j

theorem hpThetaJensenCellsBatch066_cellIntegral_bounds
    (j : Fin 20) (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
    (((1320 : ℝ) + (j.val : ℝ)) / 1600) ^ m * hpThetaJensenCellsBatch066Lower j.val *
        ((((1320 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((1320 : ℝ) + (j.val : ℝ)) / 1600)) ≤
      (∫ u : ℝ in Set.Ioo (((1320 : ℝ) + (j.val : ℝ)) / 1600)
        (((1320 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (((1320 : ℝ) + (j.val : ℝ)) / 1600)
        (((1320 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ≤
        (((1320 : ℝ) + (j.val : ℝ) + 1) / 1600) ^ m * hpThetaJensenCellsBatch066Upper j.val *
          ((((1320 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((1320 : ℝ) + (j.val : ℝ)) / 1600)) := by
  apply hpThetaJensen_cellIntegral_bounds m hm
  · positivity
  · linarith
  · fin_cases j <;> norm_num [hpThetaJensenCellsBatch066Lower]
  · exact hpThetaJensenCellsBatch066_bounds j

theorem hpThetaJensenCellsBatch067_cellIntegral_bounds
    (j : Fin 20) (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
    (((1340 : ℝ) + (j.val : ℝ)) / 1600) ^ m * hpThetaJensenCellsBatch067Lower j.val *
        ((((1340 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((1340 : ℝ) + (j.val : ℝ)) / 1600)) ≤
      (∫ u : ℝ in Set.Ioo (((1340 : ℝ) + (j.val : ℝ)) / 1600)
        (((1340 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (((1340 : ℝ) + (j.val : ℝ)) / 1600)
        (((1340 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ≤
        (((1340 : ℝ) + (j.val : ℝ) + 1) / 1600) ^ m * hpThetaJensenCellsBatch067Upper j.val *
          ((((1340 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((1340 : ℝ) + (j.val : ℝ)) / 1600)) := by
  apply hpThetaJensen_cellIntegral_bounds m hm
  · positivity
  · linarith
  · fin_cases j <;> norm_num [hpThetaJensenCellsBatch067Lower]
  · exact hpThetaJensenCellsBatch067_bounds j

theorem hpThetaJensenCellsBatch068_cellIntegral_bounds
    (j : Fin 20) (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
    (((1360 : ℝ) + (j.val : ℝ)) / 1600) ^ m * hpThetaJensenCellsBatch068Lower j.val *
        ((((1360 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((1360 : ℝ) + (j.val : ℝ)) / 1600)) ≤
      (∫ u : ℝ in Set.Ioo (((1360 : ℝ) + (j.val : ℝ)) / 1600)
        (((1360 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (((1360 : ℝ) + (j.val : ℝ)) / 1600)
        (((1360 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ≤
        (((1360 : ℝ) + (j.val : ℝ) + 1) / 1600) ^ m * hpThetaJensenCellsBatch068Upper j.val *
          ((((1360 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((1360 : ℝ) + (j.val : ℝ)) / 1600)) := by
  apply hpThetaJensen_cellIntegral_bounds m hm
  · positivity
  · linarith
  · fin_cases j <;> norm_num [hpThetaJensenCellsBatch068Lower]
  · exact hpThetaJensenCellsBatch068_bounds j

theorem hpThetaJensenCellsBatch069_cellIntegral_bounds
    (j : Fin 20) (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
    (((1380 : ℝ) + (j.val : ℝ)) / 1600) ^ m * hpThetaJensenCellsBatch069Lower j.val *
        ((((1380 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((1380 : ℝ) + (j.val : ℝ)) / 1600)) ≤
      (∫ u : ℝ in Set.Ioo (((1380 : ℝ) + (j.val : ℝ)) / 1600)
        (((1380 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (((1380 : ℝ) + (j.val : ℝ)) / 1600)
        (((1380 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ≤
        (((1380 : ℝ) + (j.val : ℝ) + 1) / 1600) ^ m * hpThetaJensenCellsBatch069Upper j.val *
          ((((1380 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((1380 : ℝ) + (j.val : ℝ)) / 1600)) := by
  apply hpThetaJensen_cellIntegral_bounds m hm
  · positivity
  · linarith
  · fin_cases j <;> norm_num [hpThetaJensenCellsBatch069Lower]
  · exact hpThetaJensenCellsBatch069_bounds j

theorem hpThetaJensenCellsBatch070_cellIntegral_bounds
    (j : Fin 20) (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
    (((1400 : ℝ) + (j.val : ℝ)) / 1600) ^ m * hpThetaJensenCellsBatch070Lower j.val *
        ((((1400 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((1400 : ℝ) + (j.val : ℝ)) / 1600)) ≤
      (∫ u : ℝ in Set.Ioo (((1400 : ℝ) + (j.val : ℝ)) / 1600)
        (((1400 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (((1400 : ℝ) + (j.val : ℝ)) / 1600)
        (((1400 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ≤
        (((1400 : ℝ) + (j.val : ℝ) + 1) / 1600) ^ m * hpThetaJensenCellsBatch070Upper j.val *
          ((((1400 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((1400 : ℝ) + (j.val : ℝ)) / 1600)) := by
  apply hpThetaJensen_cellIntegral_bounds m hm
  · positivity
  · linarith
  · fin_cases j <;> norm_num [hpThetaJensenCellsBatch070Lower]
  · exact hpThetaJensenCellsBatch070_bounds j

theorem hpThetaJensenCellsBatch071_cellIntegral_bounds
    (j : Fin 20) (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
    (((1420 : ℝ) + (j.val : ℝ)) / 1600) ^ m * hpThetaJensenCellsBatch071Lower j.val *
        ((((1420 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((1420 : ℝ) + (j.val : ℝ)) / 1600)) ≤
      (∫ u : ℝ in Set.Ioo (((1420 : ℝ) + (j.val : ℝ)) / 1600)
        (((1420 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (((1420 : ℝ) + (j.val : ℝ)) / 1600)
        (((1420 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ≤
        (((1420 : ℝ) + (j.val : ℝ) + 1) / 1600) ^ m * hpThetaJensenCellsBatch071Upper j.val *
          ((((1420 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((1420 : ℝ) + (j.val : ℝ)) / 1600)) := by
  apply hpThetaJensen_cellIntegral_bounds m hm
  · positivity
  · linarith
  · fin_cases j <;> norm_num [hpThetaJensenCellsBatch071Lower]
  · exact hpThetaJensenCellsBatch071_bounds j

theorem hpThetaJensenCellsBatch072_cellIntegral_bounds
    (j : Fin 20) (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
    (((1440 : ℝ) + (j.val : ℝ)) / 1600) ^ m * hpThetaJensenCellsBatch072Lower j.val *
        ((((1440 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((1440 : ℝ) + (j.val : ℝ)) / 1600)) ≤
      (∫ u : ℝ in Set.Ioo (((1440 : ℝ) + (j.val : ℝ)) / 1600)
        (((1440 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (((1440 : ℝ) + (j.val : ℝ)) / 1600)
        (((1440 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ≤
        (((1440 : ℝ) + (j.val : ℝ) + 1) / 1600) ^ m * hpThetaJensenCellsBatch072Upper j.val *
          ((((1440 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((1440 : ℝ) + (j.val : ℝ)) / 1600)) := by
  apply hpThetaJensen_cellIntegral_bounds m hm
  · positivity
  · linarith
  · fin_cases j <;> norm_num [hpThetaJensenCellsBatch072Lower]
  · exact hpThetaJensenCellsBatch072_bounds j

theorem hpThetaJensenCellsBatch073_cellIntegral_bounds
    (j : Fin 20) (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
    (((1460 : ℝ) + (j.val : ℝ)) / 1600) ^ m * hpThetaJensenCellsBatch073Lower j.val *
        ((((1460 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((1460 : ℝ) + (j.val : ℝ)) / 1600)) ≤
      (∫ u : ℝ in Set.Ioo (((1460 : ℝ) + (j.val : ℝ)) / 1600)
        (((1460 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (((1460 : ℝ) + (j.val : ℝ)) / 1600)
        (((1460 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ≤
        (((1460 : ℝ) + (j.val : ℝ) + 1) / 1600) ^ m * hpThetaJensenCellsBatch073Upper j.val *
          ((((1460 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((1460 : ℝ) + (j.val : ℝ)) / 1600)) := by
  apply hpThetaJensen_cellIntegral_bounds m hm
  · positivity
  · linarith
  · fin_cases j <;> norm_num [hpThetaJensenCellsBatch073Lower]
  · exact hpThetaJensenCellsBatch073_bounds j

theorem hpThetaJensenCellsBatch074_cellIntegral_bounds
    (j : Fin 20) (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
    (((1480 : ℝ) + (j.val : ℝ)) / 1600) ^ m * hpThetaJensenCellsBatch074Lower j.val *
        ((((1480 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((1480 : ℝ) + (j.val : ℝ)) / 1600)) ≤
      (∫ u : ℝ in Set.Ioo (((1480 : ℝ) + (j.val : ℝ)) / 1600)
        (((1480 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (((1480 : ℝ) + (j.val : ℝ)) / 1600)
        (((1480 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ≤
        (((1480 : ℝ) + (j.val : ℝ) + 1) / 1600) ^ m * hpThetaJensenCellsBatch074Upper j.val *
          ((((1480 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((1480 : ℝ) + (j.val : ℝ)) / 1600)) := by
  apply hpThetaJensen_cellIntegral_bounds m hm
  · positivity
  · linarith
  · fin_cases j <;> norm_num [hpThetaJensenCellsBatch074Lower]
  · exact hpThetaJensenCellsBatch074_bounds j

theorem hpThetaJensenCellsBatch075_cellIntegral_bounds
    (j : Fin 20) (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
    (((1500 : ℝ) + (j.val : ℝ)) / 1600) ^ m * hpThetaJensenCellsBatch075Lower j.val *
        ((((1500 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((1500 : ℝ) + (j.val : ℝ)) / 1600)) ≤
      (∫ u : ℝ in Set.Ioo (((1500 : ℝ) + (j.val : ℝ)) / 1600)
        (((1500 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (((1500 : ℝ) + (j.val : ℝ)) / 1600)
        (((1500 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ≤
        (((1500 : ℝ) + (j.val : ℝ) + 1) / 1600) ^ m * hpThetaJensenCellsBatch075Upper j.val *
          ((((1500 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((1500 : ℝ) + (j.val : ℝ)) / 1600)) := by
  apply hpThetaJensen_cellIntegral_bounds m hm
  · positivity
  · linarith
  · fin_cases j <;> norm_num [hpThetaJensenCellsBatch075Lower]
  · exact hpThetaJensenCellsBatch075_bounds j

theorem hpThetaJensenCellsBatch076_cellIntegral_bounds
    (j : Fin 20) (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
    (((1520 : ℝ) + (j.val : ℝ)) / 1600) ^ m * hpThetaJensenCellsBatch076Lower j.val *
        ((((1520 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((1520 : ℝ) + (j.val : ℝ)) / 1600)) ≤
      (∫ u : ℝ in Set.Ioo (((1520 : ℝ) + (j.val : ℝ)) / 1600)
        (((1520 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (((1520 : ℝ) + (j.val : ℝ)) / 1600)
        (((1520 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ≤
        (((1520 : ℝ) + (j.val : ℝ) + 1) / 1600) ^ m * hpThetaJensenCellsBatch076Upper j.val *
          ((((1520 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((1520 : ℝ) + (j.val : ℝ)) / 1600)) := by
  apply hpThetaJensen_cellIntegral_bounds m hm
  · positivity
  · linarith
  · fin_cases j <;> norm_num [hpThetaJensenCellsBatch076Lower]
  · exact hpThetaJensenCellsBatch076_bounds j

theorem hpThetaJensenCellsBatch077_cellIntegral_bounds
    (j : Fin 20) (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
    (((1540 : ℝ) + (j.val : ℝ)) / 1600) ^ m * hpThetaJensenCellsBatch077Lower j.val *
        ((((1540 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((1540 : ℝ) + (j.val : ℝ)) / 1600)) ≤
      (∫ u : ℝ in Set.Ioo (((1540 : ℝ) + (j.val : ℝ)) / 1600)
        (((1540 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (((1540 : ℝ) + (j.val : ℝ)) / 1600)
        (((1540 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ≤
        (((1540 : ℝ) + (j.val : ℝ) + 1) / 1600) ^ m * hpThetaJensenCellsBatch077Upper j.val *
          ((((1540 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((1540 : ℝ) + (j.val : ℝ)) / 1600)) := by
  apply hpThetaJensen_cellIntegral_bounds m hm
  · positivity
  · linarith
  · fin_cases j <;> norm_num [hpThetaJensenCellsBatch077Lower]
  · exact hpThetaJensenCellsBatch077_bounds j

theorem hpThetaJensenCellsBatch078_cellIntegral_bounds
    (j : Fin 20) (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
    (((1560 : ℝ) + (j.val : ℝ)) / 1600) ^ m * hpThetaJensenCellsBatch078Lower j.val *
        ((((1560 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((1560 : ℝ) + (j.val : ℝ)) / 1600)) ≤
      (∫ u : ℝ in Set.Ioo (((1560 : ℝ) + (j.val : ℝ)) / 1600)
        (((1560 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (((1560 : ℝ) + (j.val : ℝ)) / 1600)
        (((1560 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ≤
        (((1560 : ℝ) + (j.val : ℝ) + 1) / 1600) ^ m * hpThetaJensenCellsBatch078Upper j.val *
          ((((1560 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((1560 : ℝ) + (j.val : ℝ)) / 1600)) := by
  apply hpThetaJensen_cellIntegral_bounds m hm
  · positivity
  · linarith
  · fin_cases j <;> norm_num [hpThetaJensenCellsBatch078Lower]
  · exact hpThetaJensenCellsBatch078_bounds j

theorem hpThetaJensenCellsBatch079_cellIntegral_bounds
    (j : Fin 20) (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
    (((1580 : ℝ) + (j.val : ℝ)) / 1600) ^ m * hpThetaJensenCellsBatch079Lower j.val *
        ((((1580 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((1580 : ℝ) + (j.val : ℝ)) / 1600)) ≤
      (∫ u : ℝ in Set.Ioo (((1580 : ℝ) + (j.val : ℝ)) / 1600)
        (((1580 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo (((1580 : ℝ) + (j.val : ℝ)) / 1600)
        (((1580 : ℝ) + (j.val : ℝ) + 1) / 1600), u ^ m * hpRiemannThetaDifferentialKernel u) ≤
        (((1580 : ℝ) + (j.val : ℝ) + 1) / 1600) ^ m * hpThetaJensenCellsBatch079Upper j.val *
          ((((1580 : ℝ) + (j.val : ℝ) + 1) / 1600) - (((1580 : ℝ) + (j.val : ℝ)) / 1600)) := by
  apply hpThetaJensen_cellIntegral_bounds m hm
  · positivity
  · linarith
  · fin_cases j <;> norm_num [hpThetaJensenCellsBatch079Lower]
  · exact hpThetaJensenCellsBatch079_bounds j

#print axioms hpThetaJensen_powerIntegrand_integrableOn
#print axioms hpThetaJensen_cellIntegral_bounds
#print axioms hpThetaJensenCellsBatch000_cellIntegral_bounds
#print axioms hpThetaJensenCellsBatch001_cellIntegral_bounds
#print axioms hpThetaJensenCellsBatch002_cellIntegral_bounds
#print axioms hpThetaJensenCellsBatch003_cellIntegral_bounds
#print axioms hpThetaJensenCellsBatch004_cellIntegral_bounds
#print axioms hpThetaJensenCellsBatch005_cellIntegral_bounds
#print axioms hpThetaJensenCellsBatch006_cellIntegral_bounds
#print axioms hpThetaJensenCellsBatch007_cellIntegral_bounds
#print axioms hpThetaJensenCellsBatch008_cellIntegral_bounds
#print axioms hpThetaJensenCellsBatch009_cellIntegral_bounds
#print axioms hpThetaJensenCellsBatch010_cellIntegral_bounds
#print axioms hpThetaJensenCellsBatch011_cellIntegral_bounds
#print axioms hpThetaJensenCellsBatch012_cellIntegral_bounds
#print axioms hpThetaJensenCellsBatch013_cellIntegral_bounds
#print axioms hpThetaJensenCellsBatch014_cellIntegral_bounds
#print axioms hpThetaJensenCellsBatch015_cellIntegral_bounds
#print axioms hpThetaJensenCellsBatch016_cellIntegral_bounds
#print axioms hpThetaJensenCellsBatch017_cellIntegral_bounds
#print axioms hpThetaJensenCellsBatch018_cellIntegral_bounds
#print axioms hpThetaJensenCellsBatch019_cellIntegral_bounds
#print axioms hpThetaJensenCellsBatch020_cellIntegral_bounds
#print axioms hpThetaJensenCellsBatch021_cellIntegral_bounds
#print axioms hpThetaJensenCellsBatch022_cellIntegral_bounds
#print axioms hpThetaJensenCellsBatch023_cellIntegral_bounds
#print axioms hpThetaJensenCellsBatch024_cellIntegral_bounds
#print axioms hpThetaJensenCellsBatch025_cellIntegral_bounds
#print axioms hpThetaJensenCellsBatch026_cellIntegral_bounds
#print axioms hpThetaJensenCellsBatch027_cellIntegral_bounds
#print axioms hpThetaJensenCellsBatch028_cellIntegral_bounds
#print axioms hpThetaJensenCellsBatch029_cellIntegral_bounds
#print axioms hpThetaJensenCellsBatch030_cellIntegral_bounds
#print axioms hpThetaJensenCellsBatch031_cellIntegral_bounds
#print axioms hpThetaJensenCellsBatch032_cellIntegral_bounds
#print axioms hpThetaJensenCellsBatch033_cellIntegral_bounds
#print axioms hpThetaJensenCellsBatch034_cellIntegral_bounds
#print axioms hpThetaJensenCellsBatch035_cellIntegral_bounds
#print axioms hpThetaJensenCellsBatch036_cellIntegral_bounds
#print axioms hpThetaJensenCellsBatch037_cellIntegral_bounds
#print axioms hpThetaJensenCellsBatch038_cellIntegral_bounds
#print axioms hpThetaJensenCellsBatch039_cellIntegral_bounds
#print axioms hpThetaJensenCellsBatch040_cellIntegral_bounds
#print axioms hpThetaJensenCellsBatch041_cellIntegral_bounds
#print axioms hpThetaJensenCellsBatch042_cellIntegral_bounds
#print axioms hpThetaJensenCellsBatch043_cellIntegral_bounds
#print axioms hpThetaJensenCellsBatch044_cellIntegral_bounds
#print axioms hpThetaJensenCellsBatch045_cellIntegral_bounds
#print axioms hpThetaJensenCellsBatch046_cellIntegral_bounds
#print axioms hpThetaJensenCellsBatch047_cellIntegral_bounds
#print axioms hpThetaJensenCellsBatch048_cellIntegral_bounds
#print axioms hpThetaJensenCellsBatch049_cellIntegral_bounds
#print axioms hpThetaJensenCellsBatch050_cellIntegral_bounds
#print axioms hpThetaJensenCellsBatch051_cellIntegral_bounds
#print axioms hpThetaJensenCellsBatch052_cellIntegral_bounds
#print axioms hpThetaJensenCellsBatch053_cellIntegral_bounds
#print axioms hpThetaJensenCellsBatch054_cellIntegral_bounds
#print axioms hpThetaJensenCellsBatch055_cellIntegral_bounds
#print axioms hpThetaJensenCellsBatch056_cellIntegral_bounds
#print axioms hpThetaJensenCellsBatch057_cellIntegral_bounds
#print axioms hpThetaJensenCellsBatch058_cellIntegral_bounds
#print axioms hpThetaJensenCellsBatch059_cellIntegral_bounds
#print axioms hpThetaJensenCellsBatch060_cellIntegral_bounds
#print axioms hpThetaJensenCellsBatch061_cellIntegral_bounds
#print axioms hpThetaJensenCellsBatch062_cellIntegral_bounds
#print axioms hpThetaJensenCellsBatch063_cellIntegral_bounds
#print axioms hpThetaJensenCellsBatch064_cellIntegral_bounds
#print axioms hpThetaJensenCellsBatch065_cellIntegral_bounds
#print axioms hpThetaJensenCellsBatch066_cellIntegral_bounds
#print axioms hpThetaJensenCellsBatch067_cellIntegral_bounds
#print axioms hpThetaJensenCellsBatch068_cellIntegral_bounds
#print axioms hpThetaJensenCellsBatch069_cellIntegral_bounds
#print axioms hpThetaJensenCellsBatch070_cellIntegral_bounds
#print axioms hpThetaJensenCellsBatch071_cellIntegral_bounds
#print axioms hpThetaJensenCellsBatch072_cellIntegral_bounds
#print axioms hpThetaJensenCellsBatch073_cellIntegral_bounds
#print axioms hpThetaJensenCellsBatch074_cellIntegral_bounds
#print axioms hpThetaJensenCellsBatch075_cellIntegral_bounds
#print axioms hpThetaJensenCellsBatch076_cellIntegral_bounds
#print axioms hpThetaJensenCellsBatch077_cellIntegral_bounds
#print axioms hpThetaJensenCellsBatch078_cellIntegral_bounds
#print axioms hpThetaJensenCellsBatch079_cellIntegral_bounds

end HodgeProofHP
