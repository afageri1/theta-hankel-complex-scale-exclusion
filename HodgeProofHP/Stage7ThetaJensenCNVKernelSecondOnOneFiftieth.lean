/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenCNVSecondCellsBatch000
import HodgeProofHP.Stage7ThetaJensenCNVSecondCellsBatch001
import HodgeProofHP.Stage7ThetaJensenCNVSecondCellsBatch002
import HodgeProofHP.Stage7ThetaJensenCNVSecondCellsBatch003
import HodgeProofHP.Stage7ThetaJensenCNVSecondCellsBatch004
import HodgeProofHP.Stage7ThetaJensenCNVSecondCellsBatch005
import HodgeProofHP.Stage7ThetaJensenCNVSecondCellsBatch006
import HodgeProofHP.Stage7ThetaJensenCNVSecondCellsBatch007
import HodgeProofHP.Stage7ThetaJensenCNVSecondCellsBatch008
import HodgeProofHP.Stage7ThetaJensenCNVSecondCellsBatch009
import HodgeProofHP.Stage7ThetaJensenCNVSecondCellsBatch010
import HodgeProofHP.Stage7ThetaJensenCNVSecondCellsBatch011
import HodgeProofHP.Stage7ThetaJensenCNVSecondCellsBatch012
import HodgeProofHP.Stage7ThetaJensenCNVSecondCellsBatch013
import HodgeProofHP.Stage7ThetaJensenCNVSecondCellsBatch014
import HodgeProofHP.Stage7ThetaJensenCNVSecondCellsBatch015
import HodgeProofHP.Stage7ThetaJensenCNVSecondCellsBatch016
import HodgeProofHP.Stage7ThetaJensenCNVSecondCellsBatch017
import HodgeProofHP.Stage7ThetaJensenCNVSecondCellsBatch018
import HodgeProofHP.Stage7ThetaJensenCNVSecondCellsBatch019

/-! Full coverage of [0, 1/50] and the actual second derivative lower bound.
Global CNV positivity is not asserted by this module. -/
noncomputable section
namespace HodgeProofHP

theorem hpThetaCNV_secondDerivative_firstTerm_ge_neg35_on_oneFiftieth :
    ∀ u : ℝ, u ∈ Set.Icc (0 : ℝ) (1 / 50) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  exact (hpThetaCNV_interval_lower_glue (hpThetaCNV_interval_lower_glue (hpThetaCNV_interval_lower_glue (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cellsBatch000
      hpThetaCNV_secondDerivative_cellsBatch001)
      (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cellsBatch002
      (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cellsBatch003
      hpThetaCNV_secondDerivative_cellsBatch004)))
      (hpThetaCNV_interval_lower_glue (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cellsBatch005
      hpThetaCNV_secondDerivative_cellsBatch006)
      (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cellsBatch007
      (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cellsBatch008
      hpThetaCNV_secondDerivative_cellsBatch009))))
      (hpThetaCNV_interval_lower_glue (hpThetaCNV_interval_lower_glue (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cellsBatch010
      hpThetaCNV_secondDerivative_cellsBatch011)
      (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cellsBatch012
      (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cellsBatch013
      hpThetaCNV_secondDerivative_cellsBatch014)))
      (hpThetaCNV_interval_lower_glue (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cellsBatch015
      hpThetaCNV_secondDerivative_cellsBatch016)
      (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cellsBatch017
      (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cellsBatch018
      hpThetaCNV_secondDerivative_cellsBatch019)))))

theorem hpThetaPhi_secondDeriv_ge_neg35_on_oneFiftieth (u : ℝ)
    (hu : u ∈ Set.Icc (0 : ℝ) (1 / 50)) :
    (-35 : ℝ) ≤ deriv (deriv hpRiemannThetaDifferentialKernel) u := by
  have hs := hpThetaGaussianKernelSecondDerivativeTerm_summable u
  have htail : 0 ≤ ∑' n : ℕ,
      hpThetaGaussianKernelSecondDerivativeTerm (hpThetaGaussianParameter (n + 1)) u :=
    tsum_nonneg (fun n => hpThetaCNV_secondDerivative_tailTerm_nonneg_nonnegative n u hu.1)
  have hfirst := hpThetaCNV_secondDerivative_firstTerm_ge_neg35_on_oneFiftieth u hu
  have hparam : hpThetaGaussianParameter 0 = Real.pi := by simp [hpThetaGaussianParameter]
  rw [hpThetaPhi_secondDeriv_eq_kernelSeries, hs.tsum_eq_zero_add, hparam]
  linarith

#print axioms hpThetaCNV_secondDerivative_firstTerm_ge_neg35_on_oneFiftieth
#print axioms hpThetaPhi_secondDeriv_ge_neg35_on_oneFiftieth
end HodgeProofHP
