import HodgeProofHP.Stage4ThetaEnergyUpperIntegralBase
import HodgeProofHP.Stage4ThetaEnergyUpperCertificateBatch20

/-! Integrate and combine twenty certified interval bounds. -/

noncomputable section

namespace HodgeProofHP

set_option maxHeartbeats 2000000 in
-- Combining twenty exact rational integral bounds.
theorem hpThetaEnergyUpper_integral_batch_20 :
    (∫ u in (1 / 2 : ℝ)..(21 / 40 : ℝ),
      hpThetaEnergyUpperIntegrand u) ≤
        (1878981190009971039 / 12800000000000000000000 : ℝ) := by
  have h0 := hpThetaEnergyUpper_interval_integral_bound
    (1 / 2 : ℝ) (401 / 800 : ℝ) (12322279 / 100000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      intro u hu
      exact hpThetaEnergyUpper_interval_400 u
        (by simpa only [zero_div, div_one] using hu.1)
        (by simpa only [zero_div, div_one] using hu.2))
  norm_num at h0
  have h1 := hpThetaEnergyUpper_interval_integral_bound
    (401 / 800 : ℝ) (201 / 400 : ℝ) (3034047 / 25000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      intro u hu
      exact hpThetaEnergyUpper_interval_401 u
        (by simpa only [zero_div, div_one] using hu.1)
        (by simpa only [zero_div, div_one] using hu.2))
  norm_num at h1
  have h2 := hpThetaEnergyUpper_interval_integral_bound
    (201 / 400 : ℝ) (403 / 800 : ℝ) (2988067 / 25000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      intro u hu
      exact hpThetaEnergyUpper_interval_402 u
        (by simpa only [zero_div, div_one] using hu.1)
        (by simpa only [zero_div, div_one] using hu.2))
  norm_num at h2
  have h3 := hpThetaEnergyUpper_interval_integral_bound
    (403 / 800 : ℝ) (101 / 200 : ℝ) (2942627 / 25000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      intro u hu
      exact hpThetaEnergyUpper_interval_403 u
        (by simpa only [zero_div, div_one] using hu.1)
        (by simpa only [zero_div, div_one] using hu.2))
  norm_num at h3
  have h4 := hpThetaEnergyUpper_interval_integral_bound
    (101 / 200 : ℝ) (81 / 160 : ℝ) (11590847 / 100000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      intro u hu
      exact hpThetaEnergyUpper_interval_404 u
        (by simpa only [zero_div, div_one] using hu.1)
        (by simpa only [zero_div, div_one] using hu.2))
  norm_num at h4
  have h5 := hpThetaEnergyUpper_interval_integral_bound
    (81 / 160 : ℝ) (203 / 400 : ℝ) (5706661 / 50000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      intro u hu
      exact hpThetaEnergyUpper_interval_405 u
        (by simpa only [zero_div, div_one] using hu.1)
        (by simpa only [zero_div, div_one] using hu.2))
  norm_num at h5
  have h6 := hpThetaEnergyUpper_interval_integral_bound
    (203 / 400 : ℝ) (407 / 800 : ℝ) (2809459 / 25000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      intro u hu
      exact hpThetaEnergyUpper_interval_406 u
        (by simpa only [zero_div, div_one] using hu.1)
        (by simpa only [zero_div, div_one] using hu.2))
  norm_num at h6
  have h7 := hpThetaEnergyUpper_interval_integral_bound
    (407 / 800 : ℝ) (51 / 100 : ℝ) (11064489 / 100000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      intro u hu
      exact hpThetaEnergyUpper_interval_407 u
        (by simpa only [zero_div, div_one] using hu.1)
        (by simpa only [zero_div, div_one] using hu.2))
  norm_num at h7
  have h8 := hpThetaEnergyUpper_interval_integral_bound
    (51 / 100 : ℝ) (409 / 800 : ℝ) (5446599 / 50000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      intro u hu
      exact hpThetaEnergyUpper_interval_408 u
        (by simpa only [zero_div, div_one] using hu.1)
        (by simpa only [zero_div, div_one] using hu.2))
  norm_num at h8
  have h9 := hpThetaEnergyUpper_interval_integral_bound
    (409 / 800 : ℝ) (41 / 80 : ℝ) (5361959 / 50000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      intro u hu
      exact hpThetaEnergyUpper_interval_409 u
        (by simpa only [zero_div, div_one] using hu.1)
        (by simpa only [zero_div, div_one] using hu.2))
  norm_num at h9
  have h10 := hpThetaEnergyUpper_interval_integral_bound
    (41 / 80 : ℝ) (411 / 800 : ℝ) (329897 / 3125000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      intro u hu
      exact hpThetaEnergyUpper_interval_410 u
        (by simpa only [zero_div, div_one] using hu.1)
        (by simpa only [zero_div, div_one] using hu.2))
  norm_num at h10
  have h11 := hpThetaEnergyUpper_interval_integral_bound
    (411 / 800 : ℝ) (103 / 200 : ℝ) (2078307 / 20000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      intro u hu
      exact hpThetaEnergyUpper_interval_411 u
        (by simpa only [zero_div, div_one] using hu.1)
        (by simpa only [zero_div, div_one] using hu.2))
  norm_num at h11
  have h12 := hpThetaEnergyUpper_interval_integral_bound
    (103 / 200 : ℝ) (413 / 800 : ℝ) (639271 / 6250000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      intro u hu
      exact hpThetaEnergyUpper_interval_412 u
        (by simpa only [zero_div, div_one] using hu.1)
        (by simpa only [zero_div, div_one] using hu.2))
  norm_num at h12
  have h13 := hpThetaEnergyUpper_interval_integral_bound
    (413 / 800 : ℝ) (207 / 400 : ℝ) (10067133 / 100000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      intro u hu
      exact hpThetaEnergyUpper_interval_413 u
        (by simpa only [zero_div, div_one] using hu.1)
        (by simpa only [zero_div, div_one] using hu.2))
  norm_num at h13
  have h14 := hpThetaEnergyUpper_interval_integral_bound
    (207 / 400 : ℝ) (83 / 160 : ℝ) (2476983 / 25000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      intro u hu
      exact hpThetaEnergyUpper_interval_414 u
        (by simpa only [zero_div, div_one] using hu.1)
        (by simpa only [zero_div, div_one] using hu.2))
  norm_num at h14
  have h15 := hpThetaEnergyUpper_interval_integral_bound
    (83 / 160 : ℝ) (13 / 25 : ℝ) (4875349 / 50000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      intro u hu
      exact hpThetaEnergyUpper_interval_415 u
        (by simpa only [zero_div, div_one] using hu.1)
        (by simpa only [zero_div, div_one] using hu.2))
  norm_num at h15
  have h16 := hpThetaEnergyUpper_interval_integral_bound
    (13 / 25 : ℝ) (417 / 800 : ℝ) (479769 / 5000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      intro u hu
      exact hpThetaEnergyUpper_interval_416 u
        (by simpa only [zero_div, div_one] using hu.1)
        (by simpa only [zero_div, div_one] using hu.2))
  norm_num at h16
  have h17 := hpThetaEnergyUpper_interval_integral_bound
    (417 / 800 : ℝ) (209 / 400 : ℝ) (590127 / 6250000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      intro u hu
      exact hpThetaEnergyUpper_interval_417 u
        (by simpa only [zero_div, div_one] using hu.1)
        (by simpa only [zero_div, div_one] using hu.2))
  norm_num at h17
  have h18 := hpThetaEnergyUpper_interval_integral_bound
    (209 / 400 : ℝ) (419 / 800 : ℝ) (4645303 / 50000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      intro u hu
      exact hpThetaEnergyUpper_interval_418 u
        (by simpa only [zero_div, div_one] using hu.1)
        (by simpa only [zero_div, div_one] using hu.2))
  norm_num at h18
  have h19 := hpThetaEnergyUpper_interval_integral_bound
    (419 / 800 : ℝ) (21 / 40 : ℝ) (457053 / 5000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      intro u hu
      exact hpThetaEnergyUpper_interval_419 u
        (by simpa only [zero_div, div_one] using hu.1)
        (by simpa only [zero_div, div_one] using hu.2))
  norm_num at h19
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (1 / 2 : ℝ)) (b := (401 / 800 : ℝ)) (c := (21 / 40 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (401 / 800 : ℝ)) (b := (201 / 400 : ℝ)) (c := (21 / 40 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (201 / 400 : ℝ)) (b := (403 / 800 : ℝ)) (c := (21 / 40 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (403 / 800 : ℝ)) (b := (101 / 200 : ℝ)) (c := (21 / 40 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (101 / 200 : ℝ)) (b := (81 / 160 : ℝ)) (c := (21 / 40 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (81 / 160 : ℝ)) (b := (203 / 400 : ℝ)) (c := (21 / 40 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (203 / 400 : ℝ)) (b := (407 / 800 : ℝ)) (c := (21 / 40 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (407 / 800 : ℝ)) (b := (51 / 100 : ℝ)) (c := (21 / 40 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (51 / 100 : ℝ)) (b := (409 / 800 : ℝ)) (c := (21 / 40 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (409 / 800 : ℝ)) (b := (41 / 80 : ℝ)) (c := (21 / 40 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (41 / 80 : ℝ)) (b := (411 / 800 : ℝ)) (c := (21 / 40 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (411 / 800 : ℝ)) (b := (103 / 200 : ℝ)) (c := (21 / 40 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (103 / 200 : ℝ)) (b := (413 / 800 : ℝ)) (c := (21 / 40 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (413 / 800 : ℝ)) (b := (207 / 400 : ℝ)) (c := (21 / 40 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (207 / 400 : ℝ)) (b := (83 / 160 : ℝ)) (c := (21 / 40 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (83 / 160 : ℝ)) (b := (13 / 25 : ℝ)) (c := (21 / 40 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (13 / 25 : ℝ)) (b := (417 / 800 : ℝ)) (c := (21 / 40 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (417 / 800 : ℝ)) (b := (209 / 400 : ℝ)) (c := (21 / 40 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (209 / 400 : ℝ)) (b := (419 / 800 : ℝ)) (c := (21 / 40 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  linarith only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19]

#print axioms hpThetaEnergyUpper_integral_batch_20

end HodgeProofHP
