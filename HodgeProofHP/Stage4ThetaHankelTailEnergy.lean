import HodgeProofHP.Stage4ThetaHankelFiniteCompactness

/-!
Finite basis energies and convergence of the remaining energy.
This module does not yet establish an operator norm remainder bound.
-/

namespace HodgeProofHP

noncomputable def hpThetaHankelFiniteBasisEnergy
    (F : Finset hpThetaHankelBasisSet) : ℝ :=
  ∑ i ∈ F,
    ‖hpThetaHankelOperator (hpThetaHankelHilbertBasis i)‖ ^ 2

noncomputable def hpThetaHankelTailEnergy
    (F : Finset hpThetaHankelBasisSet) : ℝ :=
  hpThetaFirstTraceEnergy - hpThetaHankelFiniteBasisEnergy F

theorem hpThetaHankelFiniteBasisEnergy_nonneg
    (F : Finset hpThetaHankelBasisSet) :
    0 ≤ hpThetaHankelFiniteBasisEnergy F := by
  classical
  unfold hpThetaHankelFiniteBasisEnergy
  exact Finset.sum_nonneg (fun i _ => sq_nonneg _)

theorem hpThetaHankelFiniteBasisEnergy_empty :
    hpThetaHankelFiniteBasisEnergy ∅ = 0 := by
  simp [hpThetaHankelFiniteBasisEnergy]

theorem hpThetaHankelTailEnergy_empty :
    hpThetaHankelTailEnergy ∅ = hpThetaFirstTraceEnergy := by
  simp [hpThetaHankelTailEnergy,
    hpThetaHankelFiniteBasisEnergy_empty]

theorem hpThetaHankelFiniteBasisEnergy_tendsto :
    Filter.Tendsto hpThetaHankelFiniteBasisEnergy
      Filter.atTop (nhds hpThetaFirstTraceEnergy) := by
  change Filter.Tendsto
    (fun F : Finset hpThetaHankelBasisSet =>
      ∑ i ∈ F,
        ‖hpThetaHankelOperator (hpThetaHankelHilbertBasis i)‖ ^ 2)
    Filter.atTop (nhds hpThetaFirstTraceEnergy)
  exact hpThetaHankelChosenBasis_norm_sq_hasSum_energy

theorem hpThetaHankelTailEnergy_tendsto_zero :
    Filter.Tendsto hpThetaHankelTailEnergy
      Filter.atTop (nhds (0 : ℝ)) := by
  have hconst :
      Filter.Tendsto
        (fun _ : Finset hpThetaHankelBasisSet =>
          hpThetaFirstTraceEnergy)
        Filter.atTop (nhds hpThetaFirstTraceEnergy) :=
    tendsto_const_nhds
  change Filter.Tendsto
    (fun F : Finset hpThetaHankelBasisSet =>
      hpThetaFirstTraceEnergy - hpThetaHankelFiniteBasisEnergy F)
    Filter.atTop (nhds (0 : ℝ))
  simpa only [sub_self] using
    hconst.sub hpThetaHankelFiniteBasisEnergy_tendsto

#print axioms hpThetaHankelFiniteBasisEnergy_nonneg
#print axioms hpThetaHankelFiniteBasisEnergy_tendsto
#print axioms hpThetaHankelTailEnergy_tendsto_zero

end HodgeProofHP
