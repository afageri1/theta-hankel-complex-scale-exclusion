import HodgeProofHP.Stage4ThetaHankelSpectralTraceObstruction
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn

/-!
Preparation for the even spectral product.
We prove summability of the perturbations and basic properties
of finite products. Infinite-product convergence is a later step.
-/

namespace HodgeProofHP

noncomputable def hpThetaHankelSpectralProductFactor
    (i : HPThetaHankelSpectralIndex) (z : ℂ) : ℂ :=
  1 - z ^ 2 * i.1

noncomputable def hpThetaHankelFiniteSpectralProduct
    (F : Finset HPThetaHankelSpectralIndex) (z : ℂ) : ℂ :=
  ∏ i ∈ F, hpThetaHankelSpectralProductFactor i z

theorem hpThetaHankelSpectralPerturbation_norm_summable
    (z : ℂ) :
    Summable
      (fun i : HPThetaHankelSpectralIndex => ‖-(z ^ 2 * i.1)‖) := by
  have h :=
    hpThetaHankelSpectralValues_norm_summable.mul_left ‖z ^ 2‖
  simpa only [norm_neg, norm_mul] using h

theorem hpThetaHankelSpectralFactor_sub_one_norm_summable
    (z : ℂ) :
    Summable
      (fun i : HPThetaHankelSpectralIndex =>
        ‖hpThetaHankelSpectralProductFactor i z - 1‖) := by
  have hfun :
      (fun i : HPThetaHankelSpectralIndex =>
        ‖hpThetaHankelSpectralProductFactor i z - 1‖) =
      (fun i : HPThetaHankelSpectralIndex => ‖-(z ^ 2 * i.1)‖) := by
    funext i
    unfold hpThetaHankelSpectralProductFactor
    congr 1
    ring
  rw [hfun]
  exact hpThetaHankelSpectralPerturbation_norm_summable z

theorem hpThetaHankelSpectralProductFactor_zero
    (i : HPThetaHankelSpectralIndex) :
    hpThetaHankelSpectralProductFactor i 0 = 1 := by
  simp [hpThetaHankelSpectralProductFactor]

theorem hpThetaHankelSpectralProductFactor_even
    (i : HPThetaHankelSpectralIndex) (z : ℂ) :
    hpThetaHankelSpectralProductFactor i (-z) =
      hpThetaHankelSpectralProductFactor i z := by
  simp [hpThetaHankelSpectralProductFactor]

theorem hpThetaHankelFiniteSpectralProduct_zero
    (F : Finset HPThetaHankelSpectralIndex) :
    hpThetaHankelFiniteSpectralProduct F 0 = 1 := by
  simp [hpThetaHankelFiniteSpectralProduct,
    hpThetaHankelSpectralProductFactor_zero]

theorem hpThetaHankelFiniteSpectralProduct_even
    (F : Finset HPThetaHankelSpectralIndex) (z : ℂ) :
    hpThetaHankelFiniteSpectralProduct F (-z) =
      hpThetaHankelFiniteSpectralProduct F z := by
  unfold hpThetaHankelFiniteSpectralProduct
  apply Finset.prod_congr rfl
  intro i hi
  exact hpThetaHankelSpectralProductFactor_even i z

#check Summable.hasProdUniformlyOn_one_add
#check Summable.multipliableUniformlyOn_one_add

#print axioms hpThetaHankelSpectralPerturbation_norm_summable
#print axioms hpThetaHankelSpectralFactor_sub_one_norm_summable
#print axioms hpThetaHankelFiniteSpectralProduct_zero
#print axioms hpThetaHankelFiniteSpectralProduct_even

end HodgeProofHP
