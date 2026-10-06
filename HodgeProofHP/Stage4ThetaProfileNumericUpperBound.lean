import HodgeProofHP.Stage4ThetaProfileExpCertificate

/-!
A rational upper bound for the split tangent envelope,
and the resulting unconditional second-moment bound.
-/

namespace HodgeProofHP

private theorem hpThetaProfile_tail_combined (l p : ℝ) :
    hpThetaProfileTangentTailBound l p =
      2 * Real.exp
        ((l / 2 - Real.pi * Real.exp (2 * l)) +
          (-(2 * Real.pi * Real.exp (2 * l) - 1 / 2) * (p - l))) /
        (2 * Real.pi * Real.exp (2 * l) - 1 / 2) /
        (1 - Real.exp (-Real.pi)) := by
  rw [Real.exp_add]
  unfold hpThetaProfileTangentTailBound
  ring

private theorem hpThetaProfile_div_upper
    (n N D d : ℝ)
    (hn : n ≤ N) (hN : 0 ≤ N)
    (hd : 0 < d) (hD : d ≤ D) :
    n / D ≤ N / d := by
  have hDpos : 0 < D := lt_of_lt_of_le hd hD
  have hq : 0 ≤ N / d := div_nonneg hN (le_of_lt hd)
  have hm := mul_le_mul_of_nonneg_left hD hq
  have heq : (N / d) * d = N :=
    div_mul_cancel₀ N (ne_of_gt hd)
  apply (div_le_iff₀ hDpos).2
  nlinarith

theorem hpThetaProfileTwoTenthsUpperBound_lt :
    hpThetaProfileTwoTenthsUpperBound < (27 / 2000 : ℝ) := by
  let a : ℝ := Real.pi * Real.exp (1 / 5)
  let b : ℝ := Real.pi * Real.exp (2 / 5)
  let d : ℝ := 1 - Real.exp (-Real.pi)

  have hpiL : (157 / 50 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d2
    norm_num at h ⊢
    linarith
  have hpiU : Real.pi ≤ (63 / 20 : ℝ) := by
    have h := Real.pi_lt_d2
    norm_num at h ⊢
    linarith

  have haL :
      (157 / 50 : ℝ) * (6107 / 5000) ≤ a := by
    dsimp [a]
    exact mul_le_mul hpiL
      hpThetaProfileCertificate_exp_fifth_lower
      (by norm_num) (le_of_lt Real.pi_pos)

  have haU :
      a ≤ (63 / 20 : ℝ) * (2443 / 2000) := by
    dsimp [a]
    exact mul_le_mul hpiU
      hpThetaProfileCertificate_exp_fifth_upper
      (le_of_lt (Real.exp_pos _)) (by norm_num)

  have hbL :
      (157 / 50 : ℝ) * (7459 / 5000) ≤ b := by
    dsimp [b]
    exact mul_le_mul hpiL
      hpThetaProfileCertificate_exp_twoFifths_lower
      (by norm_num) (le_of_lt Real.pi_pos)

  have he1 :
      Real.exp (-(4 / 5 : ℝ) * a) ≤ (233 / 5000 : ℝ) := by
    calc
      Real.exp (-(4 / 5 : ℝ) * a) ≤
          Real.exp (-(767 / 250 : ℝ)) :=
        Real.exp_le_exp.mpr (by nlinarith [haL])
      _ ≤ (233 / 5000 : ℝ) :=
        hpThetaProfileCertificate_exp_neg_3068_upper

  have he2 :
      (27 / 2500 : ℝ) ≤
        Real.exp ((1 / 10 : ℝ) - (6 / 5 : ℝ) * a) := by
    calc
      (27 / 2500 : ℝ) ≤
          Real.exp (-(2259 / 500 : ℝ)) :=
        hpThetaProfileCertificate_exp_neg_4518_lower
      _ ≤ Real.exp ((1 / 10 : ℝ) - (6 / 5 : ℝ) * a) :=
        Real.exp_le_exp.mpr (by nlinarith [haU])

  have he3 :
      Real.exp ((1 / 10 : ℝ) - b) ≤ (103 / 10000 : ℝ) := by
    calc
      Real.exp ((1 / 10 : ℝ) - b) ≤
          Real.exp (-(573 / 125 : ℝ)) :=
        Real.exp_le_exp.mpr (by nlinarith [hbL])
      _ ≤ (103 / 10000 : ℝ) :=
        hpThetaProfileCertificate_exp_neg_4584_upper

  have hd : (239 / 250 : ℝ) ≤ d := by
    have hExp :
        Real.exp (-Real.pi) ≤ (11 / 250 : ℝ) := by
      calc
        Real.exp (-Real.pi) ≤
            Real.exp (-(157 / 50 : ℝ)) :=
          Real.exp_le_exp.mpr (by linarith)
        _ ≤ (11 / 250 : ℝ) :=
          hpThetaProfileCertificate_exp_neg_314_upper
    dsimp [d]
    linarith

  have hk1 : (717 / 100 : ℝ) ≤ 2 * a - 1 / 2 := by
    nlinarith [haL]
  have hk2 : (443 / 50 : ℝ) ≤ 2 * b - 1 / 2 := by
    nlinarith [hbL]
  have hk1pos : 0 < 2 * a - 1 / 2 := by
    linarith
  have hk2pos : 0 < 2 * b - 1 / 2 := by
    linarith

  have hD1 :
      (717 / 100 : ℝ) * (239 / 250) ≤
        (2 * a - 1 / 2) * d :=
    mul_le_mul hk1 hd (by norm_num) (le_of_lt hk1pos)
  have hD2 :
      (443 / 50 : ℝ) * (239 / 250) ≤
        (2 * b - 1 / 2) * d :=
    mul_le_mul hk2 hd (by norm_num) (le_of_lt hk2pos)

  have hFirst :
      2 * (Real.exp (-(4 / 5 : ℝ) * a) -
          Real.exp ((1 / 10 : ℝ) - (6 / 5 : ℝ) * a)) /
          ((2 * a - 1 / 2) * d) ≤
        (2 * ((233 / 5000 : ℝ) - 27 / 2500)) /
          ((717 / 100 : ℝ) * (239 / 250)) :=
    hpThetaProfile_div_upper _ _ _ _
      (by linarith [he1, he2])
      (by norm_num) (by norm_num) hD1

  have hLast :
      2 * Real.exp ((1 / 10 : ℝ) - b) /
          ((2 * b - 1 / 2) * d) ≤
        (2 * (103 / 10000 : ℝ)) /
          ((443 / 50 : ℝ) * (239 / 250)) :=
    hpThetaProfile_div_upper _ _ _ _
      (by linarith [he3])
      (by norm_num) (by norm_num) hD2

  have h10 : 2 * (1 / 10 : ℝ) = 1 / 5 := by norm_num
  have h20 : 2 * (1 / 5 : ℝ) = 2 / 5 := by norm_num

  have hex0 :
      (1 / 10 : ℝ) / 2 - a +
        (-(2 * a - 1 / 2) * (0 - 1 / 10)) =
      -(4 / 5 : ℝ) * a := by ring
  have hex1 :
      (1 / 10 : ℝ) / 2 - a +
        (-(2 * a - 1 / 2) * (1 / 5 - 1 / 10)) =
      (1 / 10 : ℝ) - (6 / 5 : ℝ) * a := by ring
  have hex2 :
      (1 / 5 : ℝ) / 2 - b +
        (-(2 * b - 1 / 2) * (1 / 5 - 1 / 5)) =
      (1 / 10 : ℝ) - b := by ring

  have hU :
      hpThetaProfileTwoTenthsUpperBound =
        2 * (Real.exp (-(4 / 5 : ℝ) * a) -
            Real.exp ((1 / 10 : ℝ) - (6 / 5 : ℝ) * a)) /
            ((2 * a - 1 / 2) * d) +
        2 * Real.exp ((1 / 10 : ℝ) - b) /
            ((2 * b - 1 / 2) * d) := by
    unfold hpThetaProfileTwoTenthsUpperBound
      hpThetaProfileSplitUpperBound
    rw [hpThetaProfile_tail_combined,
      hpThetaProfile_tail_combined,
      hpThetaProfile_tail_combined]
    simp only [h10, h20]
    simp only [mul_assoc]
    change
      2 * Real.exp
          ((1 / 10 : ℝ) / 2 - a +
            (-(2 * a - 1 / 2) * (0 - 1 / 10))) /
          (2 * a - 1 / 2) / d -
      2 * Real.exp
          ((1 / 10 : ℝ) / 2 - a +
            (-(2 * a - 1 / 2) * (1 / 5 - 1 / 10))) /
          (2 * a - 1 / 2) / d +
      2 * Real.exp
          ((1 / 5 : ℝ) / 2 - b +
            (-(2 * b - 1 / 2) * (1 / 5 - 1 / 5))) /
          (2 * b - 1 / 2) / d = _
    rw [hex0, hex1, hex2]
    simp only [div_div]
    ring

  rw [hU]
  calc
    _ ≤
        (2 * ((233 / 5000 : ℝ) - 27 / 2500)) /
          ((717 / 100 : ℝ) * (239 / 250)) +
        (2 * (103 / 10000 : ℝ)) /
          ((443 / 50 : ℝ) * (239 / 250)) :=
      add_le_add hFirst hLast
    _ < (27 / 2000 : ℝ) := by norm_num

theorem hpThetaPhiMomentTwo_lt_twentySeven_thousandths :
    hpThetaPhiMomentTwo < (27 / 1000 : ℝ) := by
  have h := hpThetaPhiMomentTwo_le_twoTenths_upper
  have hU := hpThetaProfileTwoTenthsUpperBound_lt
  linarith

#print axioms hpThetaProfileTwoTenthsUpperBound_lt
#print axioms hpThetaPhiMomentTwo_lt_twentySeven_thousandths

end HodgeProofHP
