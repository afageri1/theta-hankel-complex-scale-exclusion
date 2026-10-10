import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic

/-!
# Bounds for rescaled Jensen coefficient weights

For d > 0, the coefficient multiplier in J(d,0)(w/d) is
choose(d,j) / d^j. It lies between zero and 1/j!.

These bounds do not assert convergence or real-rootedness.
-/

noncomputable section

namespace HodgeProofHP

def hpThetaJensenRescalingWeight (d j : ℕ) : ℝ :=
  (Nat.choose d j : ℝ) / (d : ℝ) ^ j

theorem hpThetaJensenRescalingWeight_nonneg (d j : ℕ) :
    0 ≤ hpThetaJensenRescalingWeight d j := by
  unfold hpThetaJensenRescalingWeight
  positivity

theorem hpThetaJensenRescalingWeight_zero (d : ℕ) :
    hpThetaJensenRescalingWeight d 0 = 1 := by
  simp [hpThetaJensenRescalingWeight]

theorem hpThetaJensenRescalingWeight_one (d : ℕ) (hd : 0 < d) :
    hpThetaJensenRescalingWeight d 1 = 1 := by
  have hdreal : 0 < (d : ℝ) := Nat.cast_pos.mpr hd
  simp [hpThetaJensenRescalingWeight, Nat.choose_one_right, ne_of_gt hdreal]

theorem hpThetaJensenRescalingWeight_eq_zero_of_lt
    (d j : ℕ) (hj : d < j) :
    hpThetaJensenRescalingWeight d j = 0 := by
  simp [hpThetaJensenRescalingWeight, Nat.choose_eq_zero_of_lt hj]

theorem hpThetaJensenRescalingWeight_le_factorial
    (d j : ℕ) (hd : 0 < d) :
    hpThetaJensenRescalingWeight d j ≤ 1 / (Nat.factorial j : ℝ) := by
  have hdreal : 0 < (d : ℝ) := Nat.cast_pos.mpr hd
  have hp : 0 < (d : ℝ) ^ j := pow_pos hdreal j
  unfold hpThetaJensenRescalingWeight
  apply (div_le_iff₀ hp).2
  calc
    (Nat.choose d j : ℝ) ≤ (d : ℝ) ^ j / (Nat.factorial j : ℝ) :=
      Nat.choose_le_pow_div j d
    _ = (1 / (Nat.factorial j : ℝ)) * (d : ℝ) ^ j := by ring

theorem hpThetaJensenRescalingWeight_abs_le_factorial
    (d j : ℕ) (hd : 0 < d) :
    |hpThetaJensenRescalingWeight d j| ≤ 1 / (Nat.factorial j : ℝ) := by
  rw [abs_of_nonneg (hpThetaJensenRescalingWeight_nonneg d j)]
  exact hpThetaJensenRescalingWeight_le_factorial d j hd

#print axioms hpThetaJensenRescalingWeight_nonneg
#print axioms hpThetaJensenRescalingWeight_zero
#print axioms hpThetaJensenRescalingWeight_one
#print axioms hpThetaJensenRescalingWeight_eq_zero_of_lt
#print axioms hpThetaJensenRescalingWeight_le_factorial
#print axioms hpThetaJensenRescalingWeight_abs_le_factorial

end HodgeProofHP
