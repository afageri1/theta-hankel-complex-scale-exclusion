/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenDensityCompactCoverage
import HodgeProofHP.Stage7ThetaJensenDensityExpCellsBatch000
import HodgeProofHP.Stage7ThetaJensenDensityExpCellsBatch001
import HodgeProofHP.Stage7ThetaJensenDensityExpCellsBatch002
import HodgeProofHP.Stage7ThetaJensenDensityExpCellsBatch003
import HodgeProofHP.Stage7ThetaJensenDensityExpCellsBatch004
import HodgeProofHP.Stage7ThetaJensenDensityExpCellsBatch005
import HodgeProofHP.Stage7ThetaJensenDensityExpCellsBatch006
import HodgeProofHP.Stage7ThetaJensenDensityExpCellsBatch007
import HodgeProofHP.Stage7ThetaJensenDensityExpCellsBatch008
import HodgeProofHP.Stage7ThetaJensenDensityExpCellsBatch009
import HodgeProofHP.Stage7ThetaJensenDensityExpCellsBatch010
import HodgeProofHP.Stage7ThetaJensenDensityExpCellsBatch011
import HodgeProofHP.Stage7ThetaJensenDensityExpCellsBatch012
import HodgeProofHP.Stage7ThetaJensenDensityExpCellsBatch013
import HodgeProofHP.Stage7ThetaJensenDensityExpCellsBatch014

/-! Connected middle coverage [1/10, 3/20]. The gap below 1/10 remains open. -/
noncomputable section
namespace HodgeProofHP

theorem hpThetaPhiDensityCurvature_pos_on_oneTenth_threeTwentieths :
    ∀ t ∈ Set.Icc (1 / 10 : ℝ) (3 / 20), 0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cellsBatch000
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cellsBatch001
      hpThetaDensityExpCompact_cellsBatch002))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cellsBatch003
      hpThetaDensityExpCompact_cellsBatch004)
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cellsBatch005
      hpThetaDensityExpCompact_cellsBatch006)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cellsBatch007
      hpThetaDensityExpCompact_cellsBatch008)
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cellsBatch009
      hpThetaDensityExpCompact_cellsBatch010))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cellsBatch011
      hpThetaDensityExpCompact_cellsBatch012)
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cellsBatch013
      hpThetaDensityExpCompact_cellsBatch014))))

theorem hpThetaPhiDensityCurvature_pos_on_middle_extension :
    ∀ t ∈ Set.Icc (1 / 10 : ℝ) (200001 / 1000000),
      0 < hpThetaPhiDensityCurvature t := by
  exact hpThetaDensityCells_positive_glue
    hpThetaPhiDensityCurvature_pos_on_oneTenth_threeTwentieths
    hpThetaPhiDensityCurvature_pos_on_compact_extension

#print axioms hpThetaPhiDensityCurvature_pos_on_oneTenth_threeTwentieths
#print axioms hpThetaPhiDensityCurvature_pos_on_middle_extension
end HodgeProofHP
