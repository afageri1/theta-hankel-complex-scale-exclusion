/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenDensityCompactCellsBatch000
import HodgeProofHP.Stage7ThetaJensenDensityCompactCellsBatch001
import HodgeProofHP.Stage7ThetaJensenDensityCompactCellsBatch002
import HodgeProofHP.Stage7ThetaJensenDensityCompactCellsBatch003
import HodgeProofHP.Stage7ThetaJensenDensityCompactCellsBatch004
import HodgeProofHP.Stage7ThetaJensenDensityCompactCellsBatch005
import HodgeProofHP.Stage7ThetaJensenDensityCompactCellsBatch006
import HodgeProofHP.Stage7ThetaJensenDensityCompactCellsBatch007

/-! Connected compact coverage [3/20, 1/5]. The endpoint gap remains open. -/
noncomputable section
namespace HodgeProofHP

theorem hpThetaPhiDensityCurvature_pos_on_threeTwentieths_oneFifth :
    ∀ t ∈ Set.Icc (3 / 20 : ℝ) (1 / 5), 0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityCompact_cellsBatch000
      hpThetaDensityCompact_cellsBatch001)
      (hpThetaDensityCells_positive_glue hpThetaDensityCompact_cellsBatch002
      hpThetaDensityCompact_cellsBatch003))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityCompact_cellsBatch004
      hpThetaDensityCompact_cellsBatch005)
      (hpThetaDensityCells_positive_glue hpThetaDensityCompact_cellsBatch006
      hpThetaDensityCompact_cellsBatch007)))

theorem hpThetaPhiDensityCurvature_pos_on_compact_extension :
    ∀ t ∈ Set.Icc (3 / 20 : ℝ) (200001 / 1000000),
      0 < hpThetaPhiDensityCurvature t := by
  exact hpThetaDensityCells_positive_glue
    hpThetaPhiDensityCurvature_pos_on_threeTwentieths_oneFifth
    hpThetaPhiDensityCurvature_pos_on_pilot_cell

#print axioms hpThetaPhiDensityCurvature_pos_on_threeTwentieths_oneFifth
#print axioms hpThetaPhiDensityCurvature_pos_on_compact_extension
end HodgeProofHP
