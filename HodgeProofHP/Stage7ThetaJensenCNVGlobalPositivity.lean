/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenCNVCompactCellsBatch000
import HodgeProofHP.Stage7ThetaJensenCNVCompactCellsBatch001
import HodgeProofHP.Stage7ThetaJensenCNVCompactCellsBatch002
import HodgeProofHP.Stage7ThetaJensenCNVCompactCellsBatch003
import HodgeProofHP.Stage7ThetaJensenCNVCompactCellsBatch004
import HodgeProofHP.Stage7ThetaJensenCNVCompactCellsBatch005

/-! Complete compact coverage, analytic outer range, and global CNV positivity. -/
noncomputable section
namespace HodgeProofHP

theorem hpThetaCNV_farComparisonNumerator_pos_on_compact (t : ℝ)
    (ht : t ∈ Set.Icc (1 / 50 : ℝ) (1 : ℝ)) :
    0 < hpThetaCNVFarComparisonNumerator t := by
  by_cases h0 : t ≤ (403 / 12800 : ℝ)
  · exact hpThetaCNV_compact_cellsBatch000 t ⟨ht.1, h0⟩
  by_cases h1 : t ≤ (697 / 12800 : ℝ)
  · exact hpThetaCNV_compact_cellsBatch001 t ⟨(lt_of_not_ge h0).le, h1⟩
  by_cases h2 : t ≤ (667 / 6400 : ℝ)
  · exact hpThetaCNV_compact_cellsBatch002 t ⟨(lt_of_not_ge h1).le, h2⟩
  by_cases h3 : t ≤ (701 / 3200 : ℝ)
  · exact hpThetaCNV_compact_cellsBatch003 t ⟨(lt_of_not_ge h2).le, h3⟩
  by_cases h4 : t ≤ (767 / 1600 : ℝ)
  · exact hpThetaCNV_compact_cellsBatch004 t ⟨(lt_of_not_ge h3).le, h4⟩
  exact hpThetaCNV_compact_cellsBatch005 t ⟨(lt_of_not_ge h4).le, ht.2⟩

theorem hpThetaPhiCNVTailPositive_certified : hpThetaPhiCNVTailPositive := by
  exact hpThetaPhiCNVTailPositive_of_compact_numerator
    hpThetaCNV_farComparisonNumerator_pos_on_compact

theorem hpThetaCNV_weightedTail_comparison_on_far (t : ℝ) (ht : (1 / 50 : ℝ) ≤ t) :
    hpThetaPhiWeightedTail t * |deriv hpRiemannThetaDifferentialKernel t| <
      t * hpRiemannThetaDifferentialKernel t ^ 2 := by
  by_cases houter : 1 ≤ t
  · exact hpThetaCNV_weightedTail_comparison_on_outer t houter
  · exact hpThetaCNV_far_weightedTail_comparison_of_numerator t ht
      (hpThetaCNV_farComparisonNumerator_pos_on_compact t ⟨ht, (lt_of_not_ge houter).le⟩)

#print axioms hpThetaCNV_farComparisonNumerator_pos_on_compact
#print axioms hpThetaPhiCNVTailPositive_certified
#print axioms hpThetaCNV_weightedTail_comparison_on_far
end HodgeProofHP
