import Mathlib.Tactic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# HodgeProof-HP — Stage HP.1

Concrete complex-valued `L²(ℝ, volume)` Hilbert-space foundation.
This stage introduces only the ambient space and its foundational instances.
-/

open MeasureTheory

noncomputable section

namespace HodgeProofHP

/-- The concrete ambient space `L²(ℝ, ℂ)` with Lebesgue measure. -/
abbrev HPSpace : Type :=
  MeasureTheory.Lp ℂ 2 (volume : Measure ℝ)

/- Lebesgue measure on `ℝ` is separable because the measurable space is
countably generated and volume is sigma-finite.  We register this explicitly
so the `Lp` second-countability instance does not depend on synthesis order. -/
local instance hpVolumeIsSeparable :
    MeasureTheory.IsSeparable (volume : Measure ℝ) :=
  MeasureTheory.isSeparable_of_sigmaFinite (volume : Measure ℝ)

/-- Explicit installation of the current Mathlib `Lp` topology interface. -/
local instance hpExponentOneLeTwo :
    Fact ((1 : ENNReal) ≤ 2) :=
  ⟨by norm_num⟩

local instance hpExponentTwoNeTop :
    Fact ((2 : ENNReal) ≠ ⊤) :=
  ⟨by norm_num⟩

local instance hpSpaceSecondCountable :
    SecondCountableTopology HPSpace :=
  MeasureTheory.Lp.SecondCountableTopology

#synth NormedAddCommGroup HPSpace
#synth NormedSpace ℂ HPSpace
#synth InnerProductSpace ℂ HPSpace
#synth CompleteSpace HPSpace
#synth MeasureTheory.IsSeparable (volume : Measure ℝ)
#synth SecondCountableTopology HPSpace
#synth TopologicalSpace.SeparableSpace HPSpace

theorem hpSpace_nonempty : Nonempty HPSpace := by
  infer_instance

theorem hpSpace_complete : CompleteSpace HPSpace := by
  infer_instance

theorem hpSpace_secondCountable : SecondCountableTopology HPSpace := by
  infer_instance

theorem hpSpace_separable : TopologicalSpace.SeparableSpace HPSpace := by
  infer_instance

/-- Exact closure target for the HP.1 foundation. -/
def HPStage1Foundation : Prop :=
  Nonempty HPSpace ∧
    CompleteSpace HPSpace ∧
    SecondCountableTopology HPSpace ∧
    TopologicalSpace.SeparableSpace HPSpace

theorem hpStage1Foundation_proved : HPStage1Foundation := by
  exact ⟨hpSpace_nonempty, hpSpace_complete,
    hpSpace_secondCountable, hpSpace_separable⟩

#check HPSpace
#check hpSpace_complete
#check hpSpace_secondCountable
#check hpSpace_separable
#check hpStage1Foundation_proved

#print axioms hpSpace_nonempty
#print axioms hpSpace_complete
#print axioms hpSpace_secondCountable
#print axioms hpSpace_separable
#print axioms hpStage1Foundation_proved

end HodgeProofHP
