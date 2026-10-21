/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenDensityBridgeExplicitRadius
import HodgeProofHP.Stage7ThetaJensenDensityLowerExpCoverage
import HodgeProofHP.Stage7ThetaJensenDensityTwoTermCellsBatch000
import HodgeProofHP.Stage7ThetaJensenDensityTwoTermCellsBatch001
import HodgeProofHP.Stage7ThetaJensenDensityTwoTermCellsBatch002
import HodgeProofHP.Stage7ThetaJensenDensityTwoTermCellsBatch003
import HodgeProofHP.Stage7ThetaJensenDensityTwoTermCellsBatch004
import HodgeProofHP.Stage7ThetaJensenDensityTwoTermCellsBatch005
import HodgeProofHP.Stage7ThetaJensenDensityTwoTermCellsBatch006
import HodgeProofHP.Stage7ThetaJensenDensityTwoTermCellsBatch007
import HodgeProofHP.Stage7ThetaJensenDensityTwoTermCellsBatch008
import HodgeProofHP.Stage7ThetaJensenDensityTwoTermCellsBatch009
import HodgeProofHP.Stage7ThetaJensenDensityTwoTermCellsBatch010
import HodgeProofHP.Stage7ThetaJensenDensityTwoTermCellsBatch011
import HodgeProofHP.Stage7ThetaJensenDensityTwoTermCellsBatch012
import HodgeProofHP.Stage7ThetaJensenDensityTwoTermCellsBatch013
import HodgeProofHP.Stage7ThetaJensenDensityTwoTermCellsBatch014
import HodgeProofHP.Stage7ThetaJensenDensityTwoTermCellsBatch015
import HodgeProofHP.Stage7ThetaJensenDensityTwoTermCellsBatch016
import HodgeProofHP.Stage7ThetaJensenDensityTwoTermCellsBatch017
import HodgeProofHP.Stage7ThetaJensenDensityTwoTermCellsBatch018
import HodgeProofHP.Stage7ThetaJensenDensityTwoTermCellsBatch019
import HodgeProofHP.Stage7ThetaJensenDensityTwoTermCellsBatch020
import HodgeProofHP.Stage7ThetaJensenDensityTwoTermCellsBatch021
import HodgeProofHP.Stage7ThetaJensenDensityTwoTermCellsBatch022
import HodgeProofHP.Stage7ThetaJensenDensityTwoTermCellsBatch023
import HodgeProofHP.Stage7ThetaJensenDensityTwoTermCellsBatch024
import HodgeProofHP.Stage7ThetaJensenDensityTwoTermCellsBatch025
import HodgeProofHP.Stage7ThetaJensenDensityTwoTermCellsBatch026
import HodgeProofHP.Stage7ThetaJensenDensityTwoTermCellsBatch027
import HodgeProofHP.Stage7ThetaJensenDensityTwoTermCellsBatch028
import HodgeProofHP.Stage7ThetaJensenDensityTwoTermCellsBatch029
import HodgeProofHP.Stage7ThetaJensenDensityTwoTermCellsBatch030
import HodgeProofHP.Stage7ThetaJensenDensityTwoTermCellsBatch031
import HodgeProofHP.Stage7ThetaJensenDensityTwoTermCellsBatch032
import HodgeProofHP.Stage7ThetaJensenDensityTwoTermCellsBatch033
import HodgeProofHP.Stage7ThetaJensenDensityTwoTermCellsBatch034
import HodgeProofHP.Stage7ThetaJensenDensityTwoTermCellsBatch035
import HodgeProofHP.Stage7ThetaJensenDensityTwoTermCellsBatch036
import HodgeProofHP.Stage7ThetaJensenDensityTwoTermCellsBatch037
import HodgeProofHP.Stage7ThetaJensenDensityTwoTermCellsBatch038
import HodgeProofHP.Stage7ThetaJensenDensityTwoTermCellsBatch039
import HodgeProofHP.Stage7ThetaJensenDensityTwoTermCellsBatch040
import HodgeProofHP.Stage7ThetaJensenDensityTwoTermCellsBatch041
import HodgeProofHP.Stage7ThetaJensenDensityTwoTermCellsBatch042
import HodgeProofHP.Stage7ThetaJensenDensityTwoTermCellsBatch043
import HodgeProofHP.Stage7ThetaJensenDensityTwoTermCellsBatch044
import HodgeProofHP.Stage7ThetaJensenDensityTwoTermCellsBatch045
import HodgeProofHP.Stage7ThetaJensenDensityTwoTermCellsBatch046
import HodgeProofHP.Stage7ThetaJensenDensityTwoTermCellsBatch047
import HodgeProofHP.Stage7ThetaJensenDensityTwoTermCellsBatch048

noncomputable section
namespace HodgeProofHP

theorem hpThetaPhiDensityCurvature_pos_on_oneFiftieth_twoTwentyFifths :
    ∀ t ∈ Set.Icc (1 / 50 : ℝ) (2 / 25), 0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cellsBatch000
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cellsBatch001
      hpThetaDensityTwoTermCompact_cellsBatch002))
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cellsBatch003
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cellsBatch004
      hpThetaDensityTwoTermCompact_cellsBatch005)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cellsBatch006
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cellsBatch007
      hpThetaDensityTwoTermCompact_cellsBatch008))
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cellsBatch009
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cellsBatch010
      hpThetaDensityTwoTermCompact_cellsBatch011))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cellsBatch012
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cellsBatch013
      hpThetaDensityTwoTermCompact_cellsBatch014))
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cellsBatch015
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cellsBatch016
      hpThetaDensityTwoTermCompact_cellsBatch017)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cellsBatch018
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cellsBatch019
      hpThetaDensityTwoTermCompact_cellsBatch020))
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cellsBatch021
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cellsBatch022
      hpThetaDensityTwoTermCompact_cellsBatch023)))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cellsBatch024
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cellsBatch025
      hpThetaDensityTwoTermCompact_cellsBatch026))
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cellsBatch027
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cellsBatch028
      hpThetaDensityTwoTermCompact_cellsBatch029)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cellsBatch030
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cellsBatch031
      hpThetaDensityTwoTermCompact_cellsBatch032))
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cellsBatch033
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cellsBatch034
      hpThetaDensityTwoTermCompact_cellsBatch035))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cellsBatch036
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cellsBatch037
      hpThetaDensityTwoTermCompact_cellsBatch038))
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cellsBatch039
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cellsBatch040
      hpThetaDensityTwoTermCompact_cellsBatch041)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cellsBatch042
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cellsBatch043
      hpThetaDensityTwoTermCompact_cellsBatch044))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cellsBatch045
      hpThetaDensityTwoTermCompact_cellsBatch046)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cellsBatch047
      hpThetaDensityTwoTermCompact_cellsBatch048))))))

theorem hpThetaPhiDensityCurvature_pos_on_gap_extension :
    ∀ t ∈ Set.Icc (1 / 50 : ℝ) (200001 / 1000000),
      0 < hpThetaPhiDensityCurvature t := by
  exact hpThetaDensityCells_positive_glue
    hpThetaPhiDensityCurvature_pos_on_oneFiftieth_twoTwentyFifths
    hpThetaPhiDensityCurvature_pos_on_lower_middle_extension

theorem hpThetaPhiDensityCurvature_pos_on_connected_interval :
    ∀ t ∈ Set.Ioc (0 : ℝ) (200001 / 1000000),
      0 < hpThetaPhiDensityCurvature t := by
  intro t ht
  by_cases hnear : t ≤ (1 / 50 : ℝ)
  · exact hpThetaPhiDensityCurvature_pos_on_bridge_explicit_interval t ⟨ht.1, hnear⟩
  · exact hpThetaPhiDensityCurvature_pos_on_gap_extension t
      ⟨(lt_of_not_ge hnear).le, ht.2⟩

#print axioms hpThetaPhiDensityCurvature_pos_on_oneFiftieth_twoTwentyFifths
#print axioms hpThetaPhiDensityCurvature_pos_on_gap_extension
#print axioms hpThetaPhiDensityCurvature_pos_on_connected_interval
end HodgeProofHP
