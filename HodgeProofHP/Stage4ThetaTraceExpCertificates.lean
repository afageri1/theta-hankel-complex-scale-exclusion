import HodgeProofHP.Stage4ThetaTraceEndpointLowerBound
import Mathlib.Analysis.Complex.Exponential

/-!
Taylor certificates for rational bounds on the real exponential.
Concrete arithmetic is proved by norm_num, without external numerical axioms.
-/

namespace HodgeProofHP

noncomputable def hpThetaTraceExpTaylorSum (x : ℝ) (n : ℕ) : ℝ :=
  ∑ m ∈ Finset.range n, x ^ m / (m.factorial : ℝ)

noncomputable def hpThetaTraceExpTaylorUpper (x : ℝ) (n : ℕ) : ℝ :=
  hpThetaTraceExpTaylorSum x n +
    x ^ n * ((n : ℝ) + 1) / ((n.factorial : ℝ) * (n : ℝ))

theorem hpThetaTrace_exp_lower_of_taylor
    (x q : ℝ) (n : ℕ) (hx : 0 ≤ x)
    (hcert : q ≤ hpThetaTraceExpTaylorSum x n) :
    q ≤ Real.exp x := by
  have h := Real.sum_le_exp_of_nonneg hx n
  change hpThetaTraceExpTaylorSum x n ≤ Real.exp x at h
  exact le_trans hcert h

theorem hpThetaTrace_exp_upper_of_taylor
    (x q : ℝ) (n : ℕ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hn : 0 < n)
    (hcert : hpThetaTraceExpTaylorUpper x n ≤ q) :
    Real.exp x ≤ q := by
  have h := Real.exp_bound' (x := x) (n := n) hx0 hx1 hn
  change Real.exp x ≤ hpThetaTraceExpTaylorUpper x n at h
  exact le_trans h hcert

theorem hpThetaTrace_exp_one_lower :
    (271 / 100 : ℝ) ≤ Real.exp 1 := by
  apply hpThetaTrace_exp_lower_of_taylor 1 (271 / 100) 6
  · norm_num
  · norm_num [hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]

theorem hpThetaTrace_exp_one_upper :
    Real.exp 1 ≤ (273 / 100 : ℝ) := by
  apply hpThetaTrace_exp_upper_of_taylor 1 (273 / 100) 6
  · norm_num
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper,
      hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial]

theorem hpThetaTrace_exp_half_lower :
    (164 / 100 : ℝ) ≤ Real.exp (1 / 2) := by
  apply hpThetaTrace_exp_lower_of_taylor (1 / 2) (164 / 100) 6
  · norm_num
  · norm_num [hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]

theorem hpThetaTrace_exp_half_upper :
    Real.exp (1 / 2) ≤ (165 / 100 : ℝ) := by
  apply hpThetaTrace_exp_upper_of_taylor (1 / 2) (165 / 100) 6
  · norm_num
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper,
      hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial]

#print axioms hpThetaTrace_exp_lower_of_taylor
#print axioms hpThetaTrace_exp_upper_of_taylor
#print axioms hpThetaTrace_exp_one_lower
#print axioms hpThetaTrace_exp_one_upper
#print axioms hpThetaTrace_exp_half_lower
#print axioms hpThetaTrace_exp_half_upper

end HodgeProofHP
