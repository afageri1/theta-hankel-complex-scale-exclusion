import HodgeProofHP.Stage7ThetaJensenRescalingBounds
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Limits of rescaled Jensen coefficient weights

For every fixed j, choose(d,j)/d^j tends to 1/j! as d tends to infinity.
The recurrence below uses real subtraction only after checking j ≤ d.
This is coefficient convergence, not yet compact uniform convergence.
-/

noncomputable section

open Filter
open scoped Topology

namespace HodgeProofHP

theorem hpThetaJensenRescalingWeight_succ
    (d j : ℕ) (hd : 0 < d) (hj : j ≤ d) :
    hpThetaJensenRescalingWeight d (j + 1) =
      hpThetaJensenRescalingWeight d j *
        ((1 - (j : ℝ) / (d : ℝ)) / ((j : ℝ) + 1)) := by
  have hd0 : (d : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hd)
  have hj0 : (j : ℝ) + 1 ≠ 0 := by positivity
  have hc : (Nat.choose d (j + 1) : ℝ) * ((j : ℝ) + 1) =
      (Nat.choose d j : ℝ) * ((d : ℝ) - (j : ℝ)) := by
    have h := congrArg (fun n : ℕ => (n : ℝ)) (Nat.choose_succ_right_eq d j)
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_sub hj] using h
  have hchoose : (Nat.choose d (j + 1) : ℝ) =
      (Nat.choose d j : ℝ) * ((d : ℝ) - (j : ℝ)) / ((j : ℝ) + 1) :=
    (eq_div_iff hj0).2 hc
  unfold hpThetaJensenRescalingWeight
  rw [hchoose, pow_succ]
  field_simp [hd0, hj0] <;> ring

theorem hpThetaJensenRescalingWeight_factor_tendsto (j : ℕ) :
    Tendsto (fun d : ℕ =>
      (1 - (j : ℝ) / (d : ℝ)) / ((j : ℝ) + 1))
      atTop (𝓝 (1 / ((j : ℝ) + 1))) := by
  have hdiv : Tendsto (fun d : ℕ => (j : ℝ) / (d : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (j : ℝ)
  simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub hdiv).div_const ((j : ℝ) + 1)

theorem hpThetaJensenRescalingWeight_tendsto (j : ℕ) :
    Tendsto (fun d : ℕ => hpThetaJensenRescalingWeight d j)
      atTop (𝓝 (1 / (Nat.factorial j : ℝ))) := by
  induction j with
  | zero =>
      simpa [hpThetaJensenRescalingWeight_zero] using (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
  | succ j ih =>
      have hlim : Tendsto (fun d : ℕ =>
          hpThetaJensenRescalingWeight d j *
            ((1 - (j : ℝ) / (d : ℝ)) / ((j : ℝ) + 1)))
          atTop (𝓝 (1 / (Nat.factorial (j + 1) : ℝ))) := by
        convert ih.mul (hpThetaJensenRescalingWeight_factor_tendsto j) using 1 <;>
          simp [Nat.factorial_succ] <;> ring
      have heq :
          (fun d : ℕ => hpThetaJensenRescalingWeight d (j + 1)) =ᶠ[atTop]
          (fun d : ℕ => hpThetaJensenRescalingWeight d j *
            ((1 - (j : ℝ) / (d : ℝ)) / ((j : ℝ) + 1))) := by
        filter_upwards [eventually_ge_atTop (j + 1)] with d hd
        exact hpThetaJensenRescalingWeight_succ d j (by omega) (by omega)
      exact (tendsto_congr' heq).2 hlim

#print axioms hpThetaJensenRescalingWeight_succ
#print axioms hpThetaJensenRescalingWeight_factor_tendsto
#print axioms hpThetaJensenRescalingWeight_tendsto

end HodgeProofHP
