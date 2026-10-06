import HodgeProofHP.Stage4ThetaEnergyUpperIntegralBatch00
import HodgeProofHP.Stage4ThetaEnergyUpperIntegralBatch01
import HodgeProofHP.Stage4ThetaEnergyUpperIntegralBatch02
import HodgeProofHP.Stage4ThetaEnergyUpperIntegralBatch03
import HodgeProofHP.Stage4ThetaEnergyUpperIntegralBatch04
import HodgeProofHP.Stage4ThetaEnergyUpperIntegralBatch05
import HodgeProofHP.Stage4ThetaEnergyUpperIntegralBatch06
import HodgeProofHP.Stage4ThetaEnergyUpperIntegralBatch07
import HodgeProofHP.Stage4ThetaEnergyUpperIntegralBatch08
import HodgeProofHP.Stage4ThetaEnergyUpperIntegralBatch09
import HodgeProofHP.Stage4ThetaEnergyUpperIntegralBatch10
import HodgeProofHP.Stage4ThetaEnergyUpperIntegralBatch11
import HodgeProofHP.Stage4ThetaEnergyUpperIntegralBatch12
import HodgeProofHP.Stage4ThetaEnergyUpperIntegralBatch13
import HodgeProofHP.Stage4ThetaEnergyUpperIntegralBatch14
import HodgeProofHP.Stage4ThetaEnergyUpperIntegralBatch15
import HodgeProofHP.Stage4ThetaEnergyUpperIntegralBatch16
import HodgeProofHP.Stage4ThetaEnergyUpperIntegralBatch17
import HodgeProofHP.Stage4ThetaEnergyUpperIntegralBatch18
import HodgeProofHP.Stage4ThetaEnergyUpperIntegralBatch19
import HodgeProofHP.Stage4ThetaEnergyUpperIntegralBatch20
import HodgeProofHP.Stage4ThetaEnergyUpperIntegralBatch21
import HodgeProofHP.Stage4ThetaEnergyUpperIntegralBatch22
import HodgeProofHP.Stage4ThetaEnergyUpperIntegralBatch23
import HodgeProofHP.Stage4ThetaEnergyUpperIntegralBatch24
import HodgeProofHP.Stage4ThetaEnergyUpperIntegralBatch25
import HodgeProofHP.Stage4ThetaEnergyUpperIntegralBatch26
import HodgeProofHP.Stage4ThetaEnergyUpperIntegralBatch27
import HodgeProofHP.Stage4ThetaEnergyUpperIntegralBatch28
import HodgeProofHP.Stage4ThetaEnergyUpperIntegralBatch29
import HodgeProofHP.Stage4ThetaEnergyUpperIntegralBatch30
import HodgeProofHP.Stage4ThetaEnergyUpperIntegralBatch31
import HodgeProofHP.Stage4ThetaEnergyUpperIntegralBatch32
import HodgeProofHP.Stage4ThetaEnergyUpperIntegralBatch33
import HodgeProofHP.Stage4ThetaEnergyUpperIntegralBatch34
import HodgeProofHP.Stage4ThetaEnergyUpperIntegralBatch35
import HodgeProofHP.Stage4ThetaEnergyUpperIntegralBatch36
import HodgeProofHP.Stage4ThetaEnergyUpperIntegralBatch37
import HodgeProofHP.Stage4ThetaEnergyUpperIntegralBatch38
import HodgeProofHP.Stage4ThetaEnergyUpperIntegralBatch39

/-! Certified upper bound for theta energy between zero and one. -/

noncomputable section

namespace HodgeProofHP

set_option maxHeartbeats 2000000 in
-- Combining forty previously checked rational batch bounds.
theorem hpThetaEnergyUpper_integral_zero_one_le_certificate :
    (∫ u in (0 : ℝ)..1, hpThetaEnergyUpperIntegrand u) ≤
      (1080380018191215381377 / 12800000000000000000000 : ℝ) := by
  have h0 := hpThetaEnergyUpper_integral_batch_0
  have h1 := hpThetaEnergyUpper_integral_batch_1
  have h2 := hpThetaEnergyUpper_integral_batch_2
  have h3 := hpThetaEnergyUpper_integral_batch_3
  have h4 := hpThetaEnergyUpper_integral_batch_4
  have h5 := hpThetaEnergyUpper_integral_batch_5
  have h6 := hpThetaEnergyUpper_integral_batch_6
  have h7 := hpThetaEnergyUpper_integral_batch_7
  have h8 := hpThetaEnergyUpper_integral_batch_8
  have h9 := hpThetaEnergyUpper_integral_batch_9
  have h10 := hpThetaEnergyUpper_integral_batch_10
  have h11 := hpThetaEnergyUpper_integral_batch_11
  have h12 := hpThetaEnergyUpper_integral_batch_12
  have h13 := hpThetaEnergyUpper_integral_batch_13
  have h14 := hpThetaEnergyUpper_integral_batch_14
  have h15 := hpThetaEnergyUpper_integral_batch_15
  have h16 := hpThetaEnergyUpper_integral_batch_16
  have h17 := hpThetaEnergyUpper_integral_batch_17
  have h18 := hpThetaEnergyUpper_integral_batch_18
  have h19 := hpThetaEnergyUpper_integral_batch_19
  have h20 := hpThetaEnergyUpper_integral_batch_20
  have h21 := hpThetaEnergyUpper_integral_batch_21
  have h22 := hpThetaEnergyUpper_integral_batch_22
  have h23 := hpThetaEnergyUpper_integral_batch_23
  have h24 := hpThetaEnergyUpper_integral_batch_24
  have h25 := hpThetaEnergyUpper_integral_batch_25
  have h26 := hpThetaEnergyUpper_integral_batch_26
  have h27 := hpThetaEnergyUpper_integral_batch_27
  have h28 := hpThetaEnergyUpper_integral_batch_28
  have h29 := hpThetaEnergyUpper_integral_batch_29
  have h30 := hpThetaEnergyUpper_integral_batch_30
  have h31 := hpThetaEnergyUpper_integral_batch_31
  have h32 := hpThetaEnergyUpper_integral_batch_32
  have h33 := hpThetaEnergyUpper_integral_batch_33
  have h34 := hpThetaEnergyUpper_integral_batch_34
  have h35 := hpThetaEnergyUpper_integral_batch_35
  have h36 := hpThetaEnergyUpper_integral_batch_36
  have h37 := hpThetaEnergyUpper_integral_batch_37
  have h38 := hpThetaEnergyUpper_integral_batch_38
  have h39 := hpThetaEnergyUpper_integral_batch_39
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (0 : ℝ)) (b := (1 / 40 : ℝ)) (c := (1 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (1 / 40 : ℝ)) (b := (1 / 20 : ℝ)) (c := (1 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (1 / 20 : ℝ)) (b := (3 / 40 : ℝ)) (c := (1 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (3 / 40 : ℝ)) (b := (1 / 10 : ℝ)) (c := (1 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (1 / 10 : ℝ)) (b := (1 / 8 : ℝ)) (c := (1 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (1 / 8 : ℝ)) (b := (3 / 20 : ℝ)) (c := (1 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (3 / 20 : ℝ)) (b := (7 / 40 : ℝ)) (c := (1 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (7 / 40 : ℝ)) (b := (1 / 5 : ℝ)) (c := (1 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (1 / 5 : ℝ)) (b := (9 / 40 : ℝ)) (c := (1 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (9 / 40 : ℝ)) (b := (1 / 4 : ℝ)) (c := (1 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (1 / 4 : ℝ)) (b := (11 / 40 : ℝ)) (c := (1 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (11 / 40 : ℝ)) (b := (3 / 10 : ℝ)) (c := (1 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (3 / 10 : ℝ)) (b := (13 / 40 : ℝ)) (c := (1 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (13 / 40 : ℝ)) (b := (7 / 20 : ℝ)) (c := (1 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (7 / 20 : ℝ)) (b := (3 / 8 : ℝ)) (c := (1 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (3 / 8 : ℝ)) (b := (2 / 5 : ℝ)) (c := (1 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (2 / 5 : ℝ)) (b := (17 / 40 : ℝ)) (c := (1 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (17 / 40 : ℝ)) (b := (9 / 20 : ℝ)) (c := (1 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (9 / 20 : ℝ)) (b := (19 / 40 : ℝ)) (c := (1 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (19 / 40 : ℝ)) (b := (1 / 2 : ℝ)) (c := (1 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (1 / 2 : ℝ)) (b := (21 / 40 : ℝ)) (c := (1 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (21 / 40 : ℝ)) (b := (11 / 20 : ℝ)) (c := (1 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (11 / 20 : ℝ)) (b := (23 / 40 : ℝ)) (c := (1 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (23 / 40 : ℝ)) (b := (3 / 5 : ℝ)) (c := (1 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (3 / 5 : ℝ)) (b := (5 / 8 : ℝ)) (c := (1 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (5 / 8 : ℝ)) (b := (13 / 20 : ℝ)) (c := (1 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (13 / 20 : ℝ)) (b := (27 / 40 : ℝ)) (c := (1 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (27 / 40 : ℝ)) (b := (7 / 10 : ℝ)) (c := (1 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (7 / 10 : ℝ)) (b := (29 / 40 : ℝ)) (c := (1 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (29 / 40 : ℝ)) (b := (3 / 4 : ℝ)) (c := (1 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (3 / 4 : ℝ)) (b := (31 / 40 : ℝ)) (c := (1 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (31 / 40 : ℝ)) (b := (4 / 5 : ℝ)) (c := (1 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (4 / 5 : ℝ)) (b := (33 / 40 : ℝ)) (c := (1 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (33 / 40 : ℝ)) (b := (17 / 20 : ℝ)) (c := (1 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (17 / 20 : ℝ)) (b := (7 / 8 : ℝ)) (c := (1 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (7 / 8 : ℝ)) (b := (9 / 10 : ℝ)) (c := (1 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (9 / 10 : ℝ)) (b := (37 / 40 : ℝ)) (c := (1 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (37 / 40 : ℝ)) (b := (19 / 20 : ℝ)) (c := (1 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (19 / 20 : ℝ)) (b := (39 / 40 : ℝ)) (c := (1 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  linarith only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39]

theorem hpThetaEnergyUpper_integral_zero_one_lt :
    (∫ u in (0 : ℝ)..1,
      u * hpRiemannThetaDifferentialKernel u ^ 2) <
        (169 / 2000 : ℝ) := by
  exact lt_of_le_of_lt
    hpThetaEnergyUpper_integral_zero_one_le_certificate (by norm_num)

#print axioms hpThetaEnergyUpper_integral_zero_one_le_certificate
#print axioms hpThetaEnergyUpper_integral_zero_one_lt

end HodgeProofHP
