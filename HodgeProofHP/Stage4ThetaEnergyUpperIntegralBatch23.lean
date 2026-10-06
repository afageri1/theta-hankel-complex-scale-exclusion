import HodgeProofHP.Stage4ThetaEnergyUpperIntegralBase
import HodgeProofHP.Stage4ThetaEnergyUpperCertificateBatch23

/-! Integrate and combine twenty certified interval bounds. -/

noncomputable section

namespace HodgeProofHP

set_option maxHeartbeats 2000000 in
-- Combining twenty exact rational integral bounds.
theorem hpThetaEnergyUpper_integral_batch_23 :
    (∫ u in (23 / 40 : ℝ)..(3 / 5 : ℝ),
      hpThetaEnergyUpperIntegrand u) ≤
        (16650792915624723 / 800000000000000000000 : ℝ) := by
  have h0 := hpThetaEnergyUpper_interval_integral_bound
    (23 / 40 : ℝ) (461 / 800 : ℝ) (4465853 / 100000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      intro u hu
      exact hpThetaEnergyUpper_interval_460 u
        (by simpa only [zero_div, div_one] using hu.1)
        (by simpa only [zero_div, div_one] using hu.2))
  norm_num at h0
  have h1 := hpThetaEnergyUpper_interval_integral_bound
    (461 / 800 : ℝ) (231 / 400 : ℝ) (1095711 / 25000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      intro u hu
      exact hpThetaEnergyUpper_interval_461 u
        (by simpa only [zero_div, div_one] using hu.1)
        (by simpa only [zero_div, div_one] using hu.2))
  norm_num at h1
  have h2 := hpThetaEnergyUpper_interval_integral_bound
    (231 / 400 : ℝ) (463 / 800 : ℝ) (430113 / 10000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      intro u hu
      exact hpThetaEnergyUpper_interval_462 u
        (by simpa only [zero_div, div_one] using hu.1)
        (by simpa only [zero_div, div_one] using hu.2))
  norm_num at h2
  have h3 := hpThetaEnergyUpper_interval_integral_bound
    (463 / 800 : ℝ) (29 / 50 : ℝ) (527583 / 12500000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      intro u hu
      exact hpThetaEnergyUpper_interval_463 u
        (by simpa only [zero_div, div_one] using hu.1)
        (by simpa only [zero_div, div_one] using hu.2))
  norm_num at h3
  have h4 := hpThetaEnergyUpper_interval_integral_bound
    (29 / 50 : ℝ) (93 / 160 : ℝ) (1035359 / 25000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      intro u hu
      exact hpThetaEnergyUpper_interval_464 u
        (by simpa only [zero_div, div_one] using hu.1)
        (by simpa only [zero_div, div_one] using hu.2))
  norm_num at h4
  have h5 := hpThetaEnergyUpper_interval_integral_bound
    (93 / 160 : ℝ) (233 / 400 : ℝ) (4063433 / 100000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      intro u hu
      exact hpThetaEnergyUpper_interval_465 u
        (by simpa only [zero_div, div_one] using hu.1)
        (by simpa only [zero_div, div_one] using hu.2))
  norm_num at h5
  have h6 := hpThetaEnergyUpper_interval_integral_bound
    (233 / 400 : ℝ) (467 / 800 : ℝ) (996663 / 25000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      intro u hu
      exact hpThetaEnergyUpper_interval_466 u
        (by simpa only [zero_div, div_one] using hu.1)
        (by simpa only [zero_div, div_one] using hu.2))
  norm_num at h6
  have h7 := hpThetaEnergyUpper_interval_integral_bound
    (467 / 800 : ℝ) (117 / 200 : ℝ) (3911061 / 100000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      intro u hu
      exact hpThetaEnergyUpper_interval_467 u
        (by simpa only [zero_div, div_one] using hu.1)
        (by simpa only [zero_div, div_one] using hu.2))
  norm_num at h7
  have h8 := hpThetaEnergyUpper_interval_integral_bound
    (117 / 200 : ℝ) (469 / 800 : ℝ) (153467 / 4000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      intro u hu
      exact hpThetaEnergyUpper_interval_468 u
        (by simpa only [zero_div, div_one] using hu.1)
        (by simpa only [zero_div, div_one] using hu.2))
  norm_num at h8
  have h9 := hpThetaEnergyUpper_interval_integral_bound
    (469 / 800 : ℝ) (47 / 80 : ℝ) (752689 / 20000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      intro u hu
      exact hpThetaEnergyUpper_interval_469 u
        (by simpa only [zero_div, div_one] using hu.1)
        (by simpa only [zero_div, div_one] using hu.2))
  norm_num at h9
  have h10 := hpThetaEnergyUpper_interval_integral_bound
    (47 / 80 : ℝ) (471 / 800 : ℝ) (3691377 / 100000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      intro u hu
      exact hpThetaEnergyUpper_interval_470 u
        (by simpa only [zero_div, div_one] using hu.1)
        (by simpa only [zero_div, div_one] using hu.2))
  norm_num at h10
  have h11 := hpThetaEnergyUpper_interval_integral_bound
    (471 / 800 : ℝ) (59 / 100 : ℝ) (3620451 / 100000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      intro u hu
      exact hpThetaEnergyUpper_interval_471 u
        (by simpa only [zero_div, div_one] using hu.1)
        (by simpa only [zero_div, div_one] using hu.2))
  norm_num at h11
  have h12 := hpThetaEnergyUpper_interval_integral_bound
    (59 / 100 : ℝ) (473 / 800 : ℝ) (887663 / 25000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      intro u hu
      exact hpThetaEnergyUpper_interval_472 u
        (by simpa only [zero_div, div_one] using hu.1)
        (by simpa only [zero_div, div_one] using hu.2))
  norm_num at h12
  have h13 := hpThetaEnergyUpper_interval_integral_bound
    (473 / 800 : ℝ) (237 / 400 : ℝ) (870497 / 25000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      intro u hu
      exact hpThetaEnergyUpper_interval_473 u
        (by simpa only [zero_div, div_one] using hu.1)
        (by simpa only [zero_div, div_one] using hu.2))
  norm_num at h13
  have h14 := hpThetaEnergyUpper_interval_integral_bound
    (237 / 400 : ℝ) (19 / 32 : ℝ) (341443 / 10000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      intro u hu
      exact hpThetaEnergyUpper_interval_474 u
        (by simpa only [zero_div, div_one] using hu.1)
        (by simpa only [zero_div, div_one] using hu.2))
  norm_num at h14
  have h15 := hpThetaEnergyUpper_interval_integral_bound
    (19 / 32 : ℝ) (119 / 200 : ℝ) (418493 / 12500000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      intro u hu
      exact hpThetaEnergyUpper_interval_475 u
        (by simpa only [zero_div, div_one] using hu.1)
        (by simpa only [zero_div, div_one] using hu.2))
  norm_num at h15
  have h16 := hpThetaEnergyUpper_interval_integral_bound
    (119 / 200 : ℝ) (477 / 800 : ℝ) (65651 / 2000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      intro u hu
      exact hpThetaEnergyUpper_interval_476 u
        (by simpa only [zero_div, div_one] using hu.1)
        (by simpa only [zero_div, div_one] using hu.2))
  norm_num at h16
  have h17 := hpThetaEnergyUpper_interval_integral_bound
    (477 / 800 : ℝ) (239 / 400 : ℝ) (1609113 / 50000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      intro u hu
      exact hpThetaEnergyUpper_interval_477 u
        (by simpa only [zero_div, div_one] using hu.1)
        (by simpa only [zero_div, div_one] using hu.2))
  norm_num at h17
  have h18 := hpThetaEnergyUpper_interval_integral_bound
    (239 / 400 : ℝ) (479 / 800 : ℝ) (3154951 / 100000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      intro u hu
      exact hpThetaEnergyUpper_interval_478 u
        (by simpa only [zero_div, div_one] using hu.1)
        (by simpa only [zero_div, div_one] using hu.2))
  norm_num at h18
  have h19 := hpThetaEnergyUpper_interval_integral_bound
    (479 / 800 : ℝ) (3 / 5 : ℝ) (386589 / 12500000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      intro u hu
      exact hpThetaEnergyUpper_interval_479 u
        (by simpa only [zero_div, div_one] using hu.1)
        (by simpa only [zero_div, div_one] using hu.2))
  norm_num at h19
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (23 / 40 : ℝ)) (b := (461 / 800 : ℝ)) (c := (3 / 5 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (461 / 800 : ℝ)) (b := (231 / 400 : ℝ)) (c := (3 / 5 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (231 / 400 : ℝ)) (b := (463 / 800 : ℝ)) (c := (3 / 5 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (463 / 800 : ℝ)) (b := (29 / 50 : ℝ)) (c := (3 / 5 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (29 / 50 : ℝ)) (b := (93 / 160 : ℝ)) (c := (3 / 5 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (93 / 160 : ℝ)) (b := (233 / 400 : ℝ)) (c := (3 / 5 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (233 / 400 : ℝ)) (b := (467 / 800 : ℝ)) (c := (3 / 5 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (467 / 800 : ℝ)) (b := (117 / 200 : ℝ)) (c := (3 / 5 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (117 / 200 : ℝ)) (b := (469 / 800 : ℝ)) (c := (3 / 5 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (469 / 800 : ℝ)) (b := (47 / 80 : ℝ)) (c := (3 / 5 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (47 / 80 : ℝ)) (b := (471 / 800 : ℝ)) (c := (3 / 5 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (471 / 800 : ℝ)) (b := (59 / 100 : ℝ)) (c := (3 / 5 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (59 / 100 : ℝ)) (b := (473 / 800 : ℝ)) (c := (3 / 5 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (473 / 800 : ℝ)) (b := (237 / 400 : ℝ)) (c := (3 / 5 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (237 / 400 : ℝ)) (b := (19 / 32 : ℝ)) (c := (3 / 5 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (19 / 32 : ℝ)) (b := (119 / 200 : ℝ)) (c := (3 / 5 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (119 / 200 : ℝ)) (b := (477 / 800 : ℝ)) (c := (3 / 5 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (477 / 800 : ℝ)) (b := (239 / 400 : ℝ)) (c := (3 / 5 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (239 / 400 : ℝ)) (b := (479 / 800 : ℝ)) (c := (3 / 5 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  linarith only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19]

#print axioms hpThetaEnergyUpper_integral_batch_23

end HodgeProofHP
