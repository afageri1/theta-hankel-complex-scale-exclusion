import HodgeProofHP.Stage4ThetaProfileSplitUpperBound
import HodgeProofHP.Stage4ThetaTraceExpCertificates
import HodgeProofHP.Stage4ThetaTraceExpScaling

/-!
Rational exponential certificates for the explicit split upper bound.
All numerical inequalities are checked by the Lean kernel.
-/

namespace HodgeProofHP

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem hpThetaProfileCertificate_exp_neg_upper_of_lower
    (x L q : ℝ) (hL : 0 < L)
    (hLower : L ≤ Real.exp x) (hProduct : 1 ≤ L * q) :
    Real.exp (-x) ≤ q := by
  have hprod : L * Real.exp (-x) ≤ 1 := by
    calc
      L * Real.exp (-x) ≤ Real.exp x * Real.exp (-x) :=
        mul_le_mul_of_nonneg_right hLower
          (le_of_lt (Real.exp_pos _))
      _ = 1 := by
        rw [← Real.exp_add]
        simp
  have hinv : Real.exp (-x) ≤ 1 / L := by
    apply (le_div_iff₀ hL).2
    simpa only [mul_comm] using hprod
  have hq : 1 / L ≤ q := by
    apply (div_le_iff₀ hL).2
    simpa only [mul_comm] using hProduct
  exact le_trans hinv hq

theorem hpThetaProfileCertificate_exp_fifth_lower :
    (6107 / 5000 : ℝ) ≤ Real.exp (1 / 5) := by
  exact hpThetaTrace_exp_lower_of_taylor
    (1 / 5) (6107 / 5000) 12
    (by norm_num)
    (by
      norm_num [hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])

theorem hpThetaProfileCertificate_exp_fifth_upper :
    Real.exp (1 / 5) ≤ (2443 / 2000 : ℝ) := by
  exact hpThetaTrace_exp_upper_of_taylor
    (1 / 5) (2443 / 2000) 12
    (by norm_num) (by norm_num) (by norm_num)
    (by
      norm_num [hpThetaTraceExpTaylorSum,
        hpThetaTraceExpTaylorUpper,
        Finset.sum_range_succ, Nat.factorial])

theorem hpThetaProfileCertificate_exp_twoFifths_lower :
    (7459 / 5000 : ℝ) ≤ Real.exp (2 / 5) := by
  exact hpThetaTrace_exp_lower_of_taylor
    (2 / 5) (7459 / 5000) 12
    (by norm_num)
    (by
      norm_num [hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])

theorem hpThetaProfileCertificate_exp_twoFifths_upper :
    Real.exp (2 / 5) ≤ (14919 / 10000 : ℝ) := by
  exact hpThetaTrace_exp_upper_of_taylor
    (2 / 5) (14919 / 10000) 12
    (by norm_num) (by norm_num) (by norm_num)
    (by
      norm_num [hpThetaTraceExpTaylorSum,
        hpThetaTraceExpTaylorUpper,
        Finset.sum_range_succ, Nat.factorial])

theorem hpThetaProfileCertificate_exp_neg_3068_upper :
    Real.exp (-(767 / 250 : ℝ)) ≤ (233 / 5000 : ℝ) := by
  apply hpThetaProfileCertificate_exp_neg_upper_of_lower
    (767 / 250) (2147 / 100) (233 / 5000)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (767 / 250) (2147 / 100) 12
      (by norm_num)
      (by
        norm_num [hpThetaTraceExpTaylorSum,
          Finset.sum_range_succ, Nat.factorial])
  · norm_num

theorem hpThetaProfileCertificate_exp_neg_4584_upper :
    Real.exp (-(573 / 125 : ℝ)) ≤ (103 / 10000 : ℝ) := by
  apply hpThetaProfileCertificate_exp_neg_upper_of_lower
    (573 / 125) (486 / 5) (103 / 10000)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (573 / 125) (486 / 5) 12
      (by norm_num)
      (by
        norm_num [hpThetaTraceExpTaylorSum,
          Finset.sum_range_succ, Nat.factorial])
  · norm_num

theorem hpThetaProfileCertificate_exp_neg_314_upper :
    Real.exp (-(157 / 50 : ℝ)) ≤ (11 / 250 : ℝ) := by
  apply hpThetaProfileCertificate_exp_neg_upper_of_lower
    (157 / 50) 23 (11 / 250)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (157 / 50) 23 12
      (by norm_num)
      (by
        norm_num [hpThetaTraceExpTaylorSum,
          Finset.sum_range_succ, Nat.factorial])
  · norm_num

theorem hpThetaProfileCertificate_exp_neg_4518_lower :
    (27 / 2500 : ℝ) ≤ Real.exp (-(2259 / 500 : ℝ)) := by
  have hUpper :
      Real.exp ((2259 / 500 : ℝ) / 16) ≤
        (331569 / 250000 : ℝ) := by
    exact hpThetaTrace_exp_upper_of_taylor
      ((2259 / 500 : ℝ) / 16) (331569 / 250000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by
        norm_num [hpThetaTraceExpTaylorSum,
          hpThetaTraceExpTaylorUpper,
          Finset.sum_range_succ, Nat.factorial])
  have h :=
    hpThetaTrace_exp_neg_nat_mul_lower
      ((2259 / 500 : ℝ) / 16)
      (331569 / 250000) (27 / 2500) 16
      (by norm_num) (by norm_num) hUpper (by norm_num)
  norm_num at h ⊢
  exact h

#print axioms hpThetaProfileCertificate_exp_fifth_lower
#print axioms hpThetaProfileCertificate_exp_fifth_upper
#print axioms hpThetaProfileCertificate_exp_twoFifths_lower
#print axioms hpThetaProfileCertificate_exp_twoFifths_upper
#print axioms hpThetaProfileCertificate_exp_neg_3068_upper
#print axioms hpThetaProfileCertificate_exp_neg_4584_upper
#print axioms hpThetaProfileCertificate_exp_neg_314_upper
#print axioms hpThetaProfileCertificate_exp_neg_4518_lower

end HodgeProofHP
