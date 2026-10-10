import HodgeProofHP.Stage7ThetaJensenPolynomialExpansion
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
# Uniform convergence of rescaled Jensen polynomials on disks

The coefficient errors have a summable disk majorant. Tannery's theorem
makes their sum tend to zero, uniformly controlling J(d,0)(w/d) - F(w).
This result does not establish real-rootedness of the Jensen polynomials.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace HodgeProofHP

def hpThetaJensenDiskError (d j : ℕ) (R : ℝ) : ℝ :=
  |hpThetaJensenRescalingWeight d j - 1 / (Nat.factorial j : ℝ)| *
    ‖(hpThetaJensenGamma j : ℂ)‖ * R ^ j

theorem hpThetaJensenDiskError_nonneg
    (d j : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    0 ≤ hpThetaJensenDiskError d j R := by
  unfold hpThetaJensenDiskError
  positivity

theorem hpThetaJensenDiskError_le_majorant
    (d j : ℕ) (R : ℝ) (hd : 0 < d) (hR : 0 ≤ R) :
    hpThetaJensenDiskError d j R ≤ hpThetaJensenDiskMajorant j R := by
  have hle := hpThetaJensenRescalingWeight_le_factorial d j hd
  have hnonneg := hpThetaJensenRescalingWeight_nonneg d j
  have habs : |hpThetaJensenRescalingWeight d j -
      1 / (Nat.factorial j : ℝ)| ≤ 1 / (Nat.factorial j : ℝ) := by
    rw [abs_of_nonpos (sub_nonpos.mpr hle)]
    linarith
  unfold hpThetaJensenDiskError hpThetaJensenDiskMajorant
  calc
    _ ≤ (1 / (Nat.factorial j : ℝ)) * ‖(hpThetaJensenGamma j : ℂ)‖ * R ^ j :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right habs (norm_nonneg _)) (pow_nonneg hR j)
    _ = _ := by ring

theorem hpThetaJensenDiskError_tendsto (j : ℕ) (R : ℝ) :
    Tendsto (fun d : ℕ => hpThetaJensenDiskError d j R) atTop (𝓝 0) := by
  have h := ((hpThetaJensenRescalingWeight_tendsto j).sub_const
    (1 / (Nat.factorial j : ℝ))).norm
  simpa [hpThetaJensenDiskError, Real.norm_eq_abs] using
    (h.mul_const ‖(hpThetaJensenGamma j : ℂ)‖).mul_const (R ^ j)

theorem hpThetaJensenDiskError_tsum_tendsto (R : ℝ) (hR : 0 ≤ R) :
    Tendsto (fun d : ℕ => ∑' j : ℕ, hpThetaJensenDiskError d j R)
      atTop (𝓝 0) := by
  have hbound : ∀ᶠ d : ℕ in atTop, ∀ j : ℕ,
      ‖hpThetaJensenDiskError d j R‖ ≤ hpThetaJensenDiskMajorant j R := by
    filter_upwards [eventually_ge_atTop 1] with d hd j
    rw [Real.norm_eq_abs, abs_of_nonneg (hpThetaJensenDiskError_nonneg d j R hR)]
    exact hpThetaJensenDiskError_le_majorant d j R (by omega) hR
  simpa using tendsto_tsum_of_dominated_convergence
    (hpThetaJensenDiskMajorant_summable R hR)
    (fun j => hpThetaJensenDiskError_tendsto j R) hbound

theorem hpThetaJensenRescaledPolynomialValue_eq_tsum (d : ℕ) (w : ℂ) :
    hpThetaJensenRescaledPolynomialValue d w =
      ∑' j : ℕ, hpThetaJensenRescaledTerm d j w := by
  rw [hpThetaJensenRescaledPolynomialValue_eq_sum]
  symm
  apply tsum_eq_sum
  intro j hj
  apply hpThetaJensenRescaledTerm_eq_zero_of_lt
  simp only [Finset.mem_range, not_lt] at hj
  omega

theorem hpThetaJensenRescaledTerm_error_norm_le_disk
    (d j : ℕ) (w : ℂ) (R : ℝ) (hw : ‖w‖ ≤ R) :
    ‖hpThetaJensenRescaledTerm d j w -
      (hpThetaJensenGamma j : ℂ) * w ^ j / (Nat.factorial j : ℂ)‖ ≤
      hpThetaJensenDiskError d j R := by
  have heq : hpThetaJensenRescaledTerm d j w -
      (hpThetaJensenGamma j : ℂ) * w ^ j / (Nat.factorial j : ℂ) =
      ((hpThetaJensenRescalingWeight d j -
        1 / (Nat.factorial j : ℝ) : ℝ) : ℂ) *
        (hpThetaJensenGamma j : ℂ) * w ^ j := by
    unfold hpThetaJensenRescaledTerm
    push_cast
    ring
  rw [heq, norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg w) hw j) (by positivity)

theorem hpThetaJensenRescaledPolynomialValue_error_le
    (d : ℕ) (w : ℂ) (R : ℝ) (hd : 0 < d) (hw : ‖w‖ ≤ R) :
    ‖hpThetaJensenRescaledPolynomialValue d w -
      hpThetaJensenGeneratingFunction w‖ ≤
      ∑' j : ℕ, hpThetaJensenDiskError d j R := by
  have hR : 0 ≤ R := (norm_nonneg w).trans hw
  have he : Summable (fun j : ℕ => hpThetaJensenDiskError d j R) :=
    (hpThetaJensenDiskMajorant_summable R hR).of_norm_bounded (fun j => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hpThetaJensenDiskError_nonneg d j R hR)]
      exact hpThetaJensenDiskError_le_majorant d j R hd hR)
  have hp : Summable (fun j : ℕ => hpThetaJensenRescaledTerm d j w) := by
    apply summable_of_ne_finset_zero (s := Finset.range (d + 1))
    intro j hj
    apply hpThetaJensenRescaledTerm_eq_zero_of_lt
    simp only [Finset.mem_range, not_lt] at hj
    omega
  have hf := (hpThetaJensenGeneratingFunction_hasSum w).summable
  have hn : Summable (fun j : ℕ => ‖hpThetaJensenRescaledTerm d j w -
      (hpThetaJensenGamma j : ℂ) * w ^ j / (Nat.factorial j : ℂ)‖) :=
    he.of_norm_bounded (fun j => by
      rw [norm_norm]
      exact hpThetaJensenRescaledTerm_error_norm_le_disk d j w R hw)
  rw [hpThetaJensenRescaledPolynomialValue_eq_tsum,
    ← (hpThetaJensenGeneratingFunction_hasSum w).tsum_eq, ← hp.tsum_sub hf]
  exact (norm_tsum_le_tsum_norm hn).trans
    (hn.tsum_le_tsum
      (fun j => hpThetaJensenRescaledTerm_error_norm_le_disk d j w R hw) he)

theorem hpThetaJensenRescaledPolynomialValue_tendstoUniformlyOn_disk
    (R : ℝ) (hR : 0 ≤ R) :
    TendstoUniformlyOn hpThetaJensenRescaledPolynomialValue
      hpThetaJensenGeneratingFunction atTop {w : ℂ | ‖w‖ ≤ R} := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have he := (tendsto_order.mp (hpThetaJensenDiskError_tsum_tendsto R hR)).2 ε hε
  filter_upwards [eventually_ge_atTop 1, he] with d hd he w hw
  rw [dist_eq_norm, norm_sub_rev]
  exact (hpThetaJensenRescaledPolynomialValue_error_le d w R (by omega) hw).trans_lt he

#print axioms hpThetaJensenDiskError_nonneg
#print axioms hpThetaJensenDiskError_le_majorant
#print axioms hpThetaJensenDiskError_tendsto
#print axioms hpThetaJensenDiskError_tsum_tendsto
#print axioms hpThetaJensenRescaledPolynomialValue_eq_tsum
#print axioms hpThetaJensenRescaledTerm_error_norm_le_disk
#print axioms hpThetaJensenRescaledPolynomialValue_error_le
#print axioms hpThetaJensenRescaledPolynomialValue_tendstoUniformlyOn_disk

end HodgeProofHP
