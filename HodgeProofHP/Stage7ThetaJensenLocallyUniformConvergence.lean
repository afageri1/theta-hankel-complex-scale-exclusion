import HodgeProofHP.Stage7ThetaJensenUniformConvergence
import HodgeProofHP.Stage6ThetaJensenPositiveAxis
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Locally uniform Jensen limits and their derivatives

Upgrade disk convergence to convergence on compact sets and locally uniformly
on the complex plane. The polynomial approximants are holomorphic, so their
first derivatives converge locally uniformly as well. The limit is not the
zero function. Transfer of zero exclusion by Hurwitz remains a proof obligation.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace HodgeProofHP

theorem hpThetaJensenRescaledPolynomialValue_tendstoUniformlyOn_compact
    (s : Set ℂ) (hs : IsCompact s) :
    TendstoUniformlyOn hpThetaJensenRescaledPolynomialValue
      hpThetaJensenGeneratingFunction atTop s := by
  obtain ⟨R, hR⟩ := hs.isBounded.exists_norm_le'
  apply (hpThetaJensenRescaledPolynomialValue_tendstoUniformlyOn_disk
    (max R 0) (le_max_right R 0)).mono
  intro w hw
  exact (hR w hw).trans (le_max_left R 0)

theorem hpThetaJensenRescaledPolynomialValue_tendstoLocallyUniformly :
    TendstoLocallyUniformly hpThetaJensenRescaledPolynomialValue
      hpThetaJensenGeneratingFunction atTop := by
  intro u hu w
  let t : Set ℂ := {z | ‖z‖ < ‖w‖ + 1}
  have ht : t ∈ 𝓝 w := by
    apply (isOpen_lt continuous_norm continuous_const).mem_nhds
    change ‖w‖ < ‖w‖ + 1
    linarith
  refine ⟨t, ht, ?_⟩
  have h := hpThetaJensenRescaledPolynomialValue_tendstoUniformlyOn_disk
    (‖w‖ + 1) (by positivity)
  filter_upwards [h u hu] with d hd z hz
  exact hd z (le_of_lt hz)

theorem hpThetaJensenRescaledPolynomialValue_tendsto (w : ℂ) :
    Tendsto (fun d : ℕ => hpThetaJensenRescaledPolynomialValue d w)
      atTop (𝓝 (hpThetaJensenGeneratingFunction w)) := by
  exact (hpThetaJensenRescaledPolynomialValue_tendstoUniformlyOn_disk
    ‖w‖ (norm_nonneg w)).tendsto_at (le_refl ‖w‖)

theorem hpThetaJensenRescaledPolynomialValue_differentiable (d : ℕ) :
    Differentiable ℂ (hpThetaJensenRescaledPolynomialValue d) := by
  have heq : hpThetaJensenRescaledPolynomialValue d =
      fun w : ℂ => ∑ j ∈ Finset.range (d + 1), hpThetaJensenRescaledTerm d j w := by
    funext w
    exact hpThetaJensenRescaledPolynomialValue_eq_sum d w
  rw [heq]
  apply Differentiable.fun_sum
  intro j hj
  unfold hpThetaJensenRescaledTerm
  fun_prop

theorem hpThetaJensenRescaledPolynomialValue_deriv_tendstoLocallyUniformly :
    TendstoLocallyUniformly
      (fun d : ℕ => deriv (hpThetaJensenRescaledPolynomialValue d))
      (deriv hpThetaJensenGeneratingFunction) atTop := by
  apply tendstoLocallyUniformlyOn_univ.mp
  have h : TendstoLocallyUniformlyOn hpThetaJensenRescaledPolynomialValue
      hpThetaJensenGeneratingFunction atTop Set.univ :=
    hpThetaJensenRescaledPolynomialValue_tendstoLocallyUniformly.tendstoLocallyUniformlyOn
  exact h.deriv
      (Eventually.of_forall (fun d =>
        (hpThetaJensenRescaledPolynomialValue_differentiable d).differentiableOn))
      isOpen_univ

theorem hpThetaJensenGeneratingFunction_zero_ne_zero :
    hpThetaJensenGeneratingFunction 0 ≠ 0 := by
  simpa using hpThetaJensenGeneratingFunction_real_ne_zero 0 (by norm_num)

theorem hpThetaJensenGeneratingFunction_not_identically_zero :
    ¬ ∀ w : ℂ, hpThetaJensenGeneratingFunction w = 0 := by
  intro h
  exact hpThetaJensenGeneratingFunction_zero_ne_zero (h 0)

#print axioms hpThetaJensenRescaledPolynomialValue_tendstoUniformlyOn_compact
#print axioms hpThetaJensenRescaledPolynomialValue_tendstoLocallyUniformly
#print axioms hpThetaJensenRescaledPolynomialValue_tendsto
#print axioms hpThetaJensenRescaledPolynomialValue_differentiable
#print axioms hpThetaJensenRescaledPolynomialValue_deriv_tendstoLocallyUniformly
#print axioms hpThetaJensenGeneratingFunction_zero_ne_zero
#print axioms hpThetaJensenGeneratingFunction_not_identically_zero

end HodgeProofHP
