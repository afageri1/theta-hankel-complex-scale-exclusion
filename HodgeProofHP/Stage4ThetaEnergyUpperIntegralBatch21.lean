import HodgeProofHP.Stage4ThetaEnergyUpperIntegralBase
import HodgeProofHP.Stage4ThetaEnergyUpperCertificateBatch21

/-! Integrate and combine twenty certified interval bounds. -/

noncomputable section

namespace HodgeProofHP

set_option maxHeartbeats 2000000 in
-- Combining twenty exact rational integral bounds.
theorem hpThetaEnergyUpper_integral_batch_21 :
    (∫ u in (21 / 40 : ℝ)..(11 / 20 : ℝ),
      hpThetaEnergyUpperIntegrand u) ≤
        (1029672528283945127 / 12800000000000000000000 : ℝ) := by
  have h0 := hpThetaEnergyUpper_interval_integral_bound
    (21 / 40 : ℝ) (421 / 800 : ℝ) (899341 / 10000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      intro u hu
      exact hpThetaEnergyUpper_interval_420 u
        (by simpa only [zero_div, div_one] using hu.1)
        (by simpa only [zero_div, div_one] using hu.2))
  norm_num at h0
  have h1 := hpThetaEnergyUpper_interval_integral_bound
    (421 / 800 : ℝ) (211 / 400 : ℝ) (1769527 / 20000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      intro u hu
      exact hpThetaEnergyUpper_interval_421 u
        (by simpa only [zero_div, div_one] using hu.1)
        (by simpa only [zero_div, div_one] using hu.2))
  norm_num at h1
  have h2 := hpThetaEnergyUpper_interval_integral_bound
    (211 / 400 : ℝ) (423 / 800 : ℝ) (271991 / 3125000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      intro u hu
      exact hpThetaEnergyUpper_interval_422 u
        (by simpa only [zero_div, div_one] using hu.1)
        (by simpa only [zero_div, div_one] using hu.2))
  norm_num at h2
  have h3 := hpThetaEnergyUpper_interval_integral_bound
    (423 / 800 : ℝ) (53 / 100 : ℝ) (8561659 / 100000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      intro u hu
      exact hpThetaEnergyUpper_interval_423 u
        (by simpa only [zero_div, div_one] using hu.1)
        (by simpa only [zero_div, div_one] using hu.2))
  norm_num at h3
  have h4 := hpThetaEnergyUpper_interval_integral_bound
    (53 / 100 : ℝ) (17 / 32 : ℝ) (168429 / 2000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      intro u hu
      exact hpThetaEnergyUpper_interval_424 u
        (by simpa only [zero_div, div_one] using hu.1)
        (by simpa only [zero_div, div_one] using hu.2))
  norm_num at h4
  have h5 := hpThetaEnergyUpper_interval_integral_bound
    (17 / 32 : ℝ) (213 / 400 : ℝ) (8283019 / 100000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      intro u hu
      exact hpThetaEnergyUpper_interval_425 u
        (by simpa only [zero_div, div_one] using hu.1)
        (by simpa only [zero_div, div_one] using hu.2))
  norm_num at h5
  have h6 := hpThetaEnergyUpper_interval_integral_bound
    (213 / 400 : ℝ) (427 / 800 : ℝ) (4073209 / 50000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      intro u hu
      exact hpThetaEnergyUpper_interval_426 u
        (by simpa only [zero_div, div_one] using hu.1)
        (by simpa only [zero_div, div_one] using hu.2))
  norm_num at h6
  have h7 := hpThetaEnergyUpper_interval_integral_bound
    (427 / 800 : ℝ) (107 / 200 : ℝ) (4005783 / 50000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      intro u hu
      exact hpThetaEnergyUpper_interval_427 u
        (by simpa only [zero_div, div_one] using hu.1)
        (by simpa only [zero_div, div_one] using hu.2))
  norm_num at h7
  have h8 := hpThetaEnergyUpper_interval_integral_bound
    (107 / 200 : ℝ) (429 / 800 : ℝ) (7878501 / 100000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      intro u hu
      exact hpThetaEnergyUpper_interval_428 u
        (by simpa only [zero_div, div_one] using hu.1)
        (by simpa only [zero_div, div_one] using hu.2))
  norm_num at h8
  have h9 := hpThetaEnergyUpper_interval_integral_bound
    (429 / 800 : ℝ) (43 / 80 : ℝ) (7747197 / 100000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      intro u hu
      exact hpThetaEnergyUpper_interval_429 u
        (by simpa only [zero_div, div_one] using hu.1)
        (by simpa only [zero_div, div_one] using hu.2))
  norm_num at h9
  have h10 := hpThetaEnergyUpper_interval_integral_bound
    (43 / 80 : ℝ) (431 / 800 : ℝ) (3808827 / 50000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      intro u hu
      exact hpThetaEnergyUpper_interval_430 u
        (by simpa only [zero_div, div_one] using hu.1)
        (by simpa only [zero_div, div_one] using hu.2))
  norm_num at h10
  have h11 := hpThetaEnergyUpper_interval_integral_bound
    (431 / 800 : ℝ) (27 / 50 : ℝ) (374489 / 5000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      intro u hu
      exact hpThetaEnergyUpper_interval_431 u
        (by simpa only [zero_div, div_one] using hu.1)
        (by simpa only [zero_div, div_one] using hu.2))
  norm_num at h11
  have h12 := hpThetaEnergyUpper_interval_integral_bound
    (27 / 50 : ℝ) (433 / 800 : ℝ) (920459 / 12500000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      intro u hu
      exact hpThetaEnergyUpper_interval_432 u
        (by simpa only [zero_div, div_one] using hu.1)
        (by simpa only [zero_div, div_one] using hu.2))
  norm_num at h12
  have h13 := hpThetaEnergyUpper_interval_integral_bound
    (433 / 800 : ℝ) (217 / 400 : ℝ) (1809809 / 25000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      intro u hu
      exact hpThetaEnergyUpper_interval_433 u
        (by simpa only [zero_div, div_one] using hu.1)
        (by simpa only [zero_div, div_one] using hu.2))
  norm_num at h13
  have h14 := hpThetaEnergyUpper_interval_integral_bound
    (217 / 400 : ℝ) (87 / 160 : ℝ) (7116479 / 100000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      intro u hu
      exact hpThetaEnergyUpper_interval_434 u
        (by simpa only [zero_div, div_one] using hu.1)
        (by simpa only [zero_div, div_one] using hu.2))
  norm_num at h14
  have h15 := hpThetaEnergyUpper_interval_integral_bound
    (87 / 160 : ℝ) (109 / 200 : ℝ) (6995397 / 100000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      intro u hu
      exact hpThetaEnergyUpper_interval_435 u
        (by simpa only [zero_div, div_one] using hu.1)
        (by simpa only [zero_div, div_one] using hu.2))
  norm_num at h15
  have h16 := hpThetaEnergyUpper_interval_integral_bound
    (109 / 200 : ℝ) (437 / 800 : ℝ) (1375189 / 20000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      intro u hu
      exact hpThetaEnergyUpper_interval_436 u
        (by simpa only [zero_div, div_one] using hu.1)
        (by simpa only [zero_div, div_one] using hu.2))
  norm_num at h16
  have h17 := hpThetaEnergyUpper_interval_integral_bound
    (437 / 800 : ℝ) (219 / 400 : ℝ) (3379073 / 50000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      intro u hu
      exact hpThetaEnergyUpper_interval_437 u
        (by simpa only [zero_div, div_one] using hu.1)
        (by simpa only [zero_div, div_one] using hu.2))
  norm_num at h17
  have h18 := hpThetaEnergyUpper_interval_integral_bound
    (219 / 400 : ℝ) (439 / 800 : ℝ) (6641967 / 100000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      intro u hu
      exact hpThetaEnergyUpper_interval_438 u
        (by simpa only [zero_div, div_one] using hu.1)
        (by simpa only [zero_div, div_one] using hu.2))
  norm_num at h18
  have h19 := hpThetaEnergyUpper_interval_integral_bound
    (439 / 800 : ℝ) (11 / 20 : ℝ) (652741 / 10000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      intro u hu
      exact hpThetaEnergyUpper_interval_439 u
        (by simpa only [zero_div, div_one] using hu.1)
        (by simpa only [zero_div, div_one] using hu.2))
  norm_num at h19
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (21 / 40 : ℝ)) (b := (421 / 800 : ℝ)) (c := (11 / 20 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (421 / 800 : ℝ)) (b := (211 / 400 : ℝ)) (c := (11 / 20 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (211 / 400 : ℝ)) (b := (423 / 800 : ℝ)) (c := (11 / 20 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (423 / 800 : ℝ)) (b := (53 / 100 : ℝ)) (c := (11 / 20 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (53 / 100 : ℝ)) (b := (17 / 32 : ℝ)) (c := (11 / 20 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (17 / 32 : ℝ)) (b := (213 / 400 : ℝ)) (c := (11 / 20 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (213 / 400 : ℝ)) (b := (427 / 800 : ℝ)) (c := (11 / 20 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (427 / 800 : ℝ)) (b := (107 / 200 : ℝ)) (c := (11 / 20 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (107 / 200 : ℝ)) (b := (429 / 800 : ℝ)) (c := (11 / 20 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (429 / 800 : ℝ)) (b := (43 / 80 : ℝ)) (c := (11 / 20 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (43 / 80 : ℝ)) (b := (431 / 800 : ℝ)) (c := (11 / 20 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (431 / 800 : ℝ)) (b := (27 / 50 : ℝ)) (c := (11 / 20 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (27 / 50 : ℝ)) (b := (433 / 800 : ℝ)) (c := (11 / 20 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (433 / 800 : ℝ)) (b := (217 / 400 : ℝ)) (c := (11 / 20 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (217 / 400 : ℝ)) (b := (87 / 160 : ℝ)) (c := (11 / 20 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (87 / 160 : ℝ)) (b := (109 / 200 : ℝ)) (c := (11 / 20 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (109 / 200 : ℝ)) (b := (437 / 800 : ℝ)) (c := (11 / 20 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (437 / 800 : ℝ)) (b := (219 / 400 : ℝ)) (c := (11 / 20 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (219 / 400 : ℝ)) (b := (439 / 800 : ℝ)) (c := (11 / 20 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  linarith only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19]

#print axioms hpThetaEnergyUpper_integral_batch_21

end HodgeProofHP
