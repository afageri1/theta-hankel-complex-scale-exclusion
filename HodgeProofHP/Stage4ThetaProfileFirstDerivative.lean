import HodgeProofHP.Stage4ThetaFirstMajorantSummable
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
Unconditional termwise differentiation of the theta log profile.
The local derivative bounds and their summability are already proved.
-/

noncomputable section

namespace HodgeProofHP

theorem hpThetaGaussianFirstTerm_norm_summable (u : ℝ) :
    Summable (fun n : ℕ => ‖hpThetaGaussianFirstTerm n u‖) := by
  exact Summable.of_nonneg_of_le
    (fun n => norm_nonneg (hpThetaGaussianFirstTerm n u))
    (fun n =>
      hpThetaGaussianFirstTerm_norm_le_majorant
        u u u n le_rfl le_rfl)
    (hpThetaGaussianFirstMajorant_summable u u)

theorem hpThetaGaussianFirstTerm_summable (u : ℝ) :
    Summable (fun n : ℕ => hpThetaGaussianFirstTerm n u) :=
  Summable.of_norm (hpThetaGaussianFirstTerm_norm_summable u)

theorem hpRiemannThetaLogProfile_hasDerivAt (u : ℝ) :
    HasDerivAt hpRiemannThetaLogProfile
      (∑' n : ℕ, hpThetaGaussianFirstTerm n u) u := by
  have hu : u ∈ Set.Ioo (u - 1) (u + 1) := by
    constructor <;> linarith
  exact hpRiemannThetaLogProfile_hasDerivAt_of_local_bound
    (Set.Ioo (u - 1) (u + 1))
    (hpThetaGaussianFirstMajorant (u - 1) (u + 1))
    isOpen_Ioo
    isPreconnected_Ioo
    (hpThetaGaussianFirstMajorant_summable (u - 1) (u + 1))
    (hpThetaGaussianFirstTerm_bound_on_Ioo (u - 1) (u + 1))
    u u hu hu

theorem hpRiemannThetaLogProfile_deriv_eq_tsum (u : ℝ) :
    deriv hpRiemannThetaLogProfile u =
      ∑' n : ℕ, hpThetaGaussianFirstTerm n u :=
  (hpRiemannThetaLogProfile_hasDerivAt u).deriv

theorem hpRiemannThetaLogProfile_deriv_function :
    deriv hpRiemannThetaLogProfile =
      fun u : ℝ => ∑' n : ℕ, hpThetaGaussianFirstTerm n u := by
  funext u
  exact hpRiemannThetaLogProfile_deriv_eq_tsum u

theorem hpRiemannThetaLogProfile_differentiable :
    Differentiable ℝ hpRiemannThetaLogProfile := by
  intro u
  exact (hpRiemannThetaLogProfile_hasDerivAt u).differentiableAt

theorem hpRiemannThetaLogProfile_continuous :
    Continuous hpRiemannThetaLogProfile :=
  hpRiemannThetaLogProfile_differentiable.continuous

#print axioms hpThetaGaussianFirstTerm_norm_summable
#print axioms hpThetaGaussianFirstTerm_summable
#print axioms hpRiemannThetaLogProfile_hasDerivAt
#print axioms hpRiemannThetaLogProfile_deriv_eq_tsum
#print axioms hpRiemannThetaLogProfile_deriv_function
#print axioms hpRiemannThetaLogProfile_differentiable
#print axioms hpRiemannThetaLogProfile_continuous

end HodgeProofHP
