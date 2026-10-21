/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenDensityTwoTermCoverage
import HodgeProofHP.Stage7ThetaJensenDensityUpperExpCellsBatch000
import HodgeProofHP.Stage7ThetaJensenDensityUpperExpCellsBatch001
import HodgeProofHP.Stage7ThetaJensenDensityUpperExpCellsBatch002
import HodgeProofHP.Stage7ThetaJensenDensityUpperExpCellsBatch003
import HodgeProofHP.Stage7ThetaJensenDensityUpperExpCellsBatch004
import HodgeProofHP.Stage7ThetaJensenDensityUpperExpCellsBatch005
import HodgeProofHP.Stage7ThetaJensenDensityUpperExpCellsBatch006
import HodgeProofHP.Stage7ThetaJensenDensityUpperExpCellsBatch007
import HodgeProofHP.Stage7ThetaJensenDensityUpperExpCellsBatch008
import HodgeProofHP.Stage7ThetaJensenDensityUpperExpCellsBatch009
import HodgeProofHP.Stage7ThetaJensenDensityUpperExpCellsBatch010
import HodgeProofHP.Stage7ThetaJensenDensityUpperExpCellsBatch011
import HodgeProofHP.Stage7ThetaJensenDensityUpperExpCellsBatch012
import HodgeProofHP.Stage7ThetaJensenDensityUpperExpCellsBatch013
import HodgeProofHP.Stage7ThetaJensenDensityUpperExpCellsBatch014
import HodgeProofHP.Stage7ThetaJensenDensityUpperExpCellsBatch015
import HodgeProofHP.Stage7ThetaJensenDensityUpperExpCellsBatch016

/-! Upper compact certificates, joined to the verified connected interval. -/
noncomputable section
namespace HodgeProofHP

theorem hpThetaPhiDensityCurvature_pos_on_oneFifth_oneHalf :
    ∀ t ∈ Set.Icc (1 / 5 : ℝ) (1 / 2), 0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cellsBatch000
      hpThetaDensityUpperExpCompact_cellsBatch001)
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cellsBatch002
      hpThetaDensityUpperExpCompact_cellsBatch003))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cellsBatch004
      hpThetaDensityUpperExpCompact_cellsBatch005)
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cellsBatch006
      hpThetaDensityUpperExpCompact_cellsBatch007)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cellsBatch008
      hpThetaDensityUpperExpCompact_cellsBatch009)
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cellsBatch010
      hpThetaDensityUpperExpCompact_cellsBatch011))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cellsBatch012
      hpThetaDensityUpperExpCompact_cellsBatch013)
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cellsBatch014
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cellsBatch015
      hpThetaDensityUpperExpCompact_cellsBatch016)))))

theorem hpThetaPhiDensityCurvature_pos_on_connected_half :
    ∀ t ∈ Set.Ioc (0 : ℝ) (1 / 2), 0 < hpThetaPhiDensityCurvature t := by
  intro t ht
  by_cases hsmall : t ≤ (200001 / 1000000 : ℝ)
  · exact hpThetaPhiDensityCurvature_pos_on_connected_interval t ⟨ht.1, hsmall⟩
  · apply hpThetaPhiDensityCurvature_pos_on_oneFifth_oneHalf t
    exact ⟨by linarith, ht.2⟩

#print axioms hpThetaPhiDensityCurvature_pos_on_oneFifth_oneHalf
#print axioms hpThetaPhiDensityCurvature_pos_on_connected_half
end HodgeProofHP
