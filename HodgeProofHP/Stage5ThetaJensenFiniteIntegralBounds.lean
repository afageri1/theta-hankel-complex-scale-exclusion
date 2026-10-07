import HodgeProofHP.Stage5ThetaJensenIntegralPartition
import Mathlib.Tactic

/-! Finite numerical bounds on (0,1), checked from the existing cell tables.
Python chooses rounded rational bounds; Lean verifies every finite sum.
Full moment bounds still require adding the previously proved tails. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaJensenBatchZeroUpper (b : ℕ) : ℝ :=
  match b with
  | 0 => (11214173359 / 500000000000 : ℝ)
  | 1 => (22373177003 / 1000000000000 : ℝ)
  | 2 => (11125409631 / 500000000000 : ℝ)
  | 3 => (5515659671 / 250000000000 : ℝ)
  | 4 => (4362084877 / 200000000000 : ℝ)
  | 5 => (21496381143 / 1000000000000 : ℝ)
  | 6 => (660097389 / 31250000000 : ℝ)
  | 7 => (20693622771 / 1000000000000 : ℝ)
  | 8 => (10105627603 / 500000000000 : ℝ)
  | 9 => (19679704491 / 1000000000000 : ℝ)
  | 10 => (9551482839 / 500000000000 : ℝ)
  | 11 => (18485302723 / 1000000000000 : ℝ)
  | 12 => (17831209339 / 1000000000000 : ℝ)
  | 13 => (17145366581 / 1000000000000 : ℝ)
  | 14 => (1643259767 / 100000000000 : ℝ)
  | 15 => (15697820653 / 1000000000000 : ℝ)
  | 16 => (934124971 / 62500000000 : ℝ)
  | 17 => (2836418923 / 200000000000 : ℝ)
  | 18 => (3352753179 / 250000000000 : ℝ)
  | 19 => (98730923 / 7812500000 : ℝ)
  | 20 => (11866385069 / 1000000000000 : ℝ)
  | 21 => (2775488041 / 250000000000 : ℝ)
  | 22 => (10348480209 / 1000000000000 : ℝ)
  | 23 => (1201239169 / 125000000000 : ℝ)
  | 24 => (2222471177 / 250000000000 : ℝ)
  | 25 => (8191686813 / 1000000000000 : ℝ)
  | 26 => (3759123721 / 500000000000 : ℝ)
  | 27 => (429506947 / 62500000000 : ℝ)
  | 28 => (6255426791 / 1000000000000 : ℝ)
  | 29 => (2834970561 / 500000000000 : ℝ)
  | 30 => (1279249639 / 250000000000 : ℝ)
  | 31 => (574693359 / 125000000000 : ℝ)
  | 32 => (205607433 / 50000000000 : ℝ)
  | 33 => (915249531 / 250000000000 : ℝ)
  | 34 => (1621971371 / 500000000000 : ℝ)
  | 35 => (2860509211 / 1000000000000 : ℝ)
  | 36 => (39217703 / 15625000000 : ℝ)
  | 37 => (1095595369 / 500000000000 : ℝ)
  | 38 => (1903034813 / 1000000000000 : ℝ)
  | 39 => (1644029113 / 1000000000000 : ℝ)
  | 40 => (1412585397 / 1000000000000 : ℝ)
  | 41 => (241399869 / 200000000000 : ℝ)
  | 42 => (1025485623 / 1000000000000 : ℝ)
  | 43 => (27069103 / 31250000000 : ℝ)
  | 44 => (727326997 / 1000000000000 : ℝ)
  | 45 => (75874421 / 125000000000 : ℝ)
  | 46 => (100683279 / 200000000000 : ℝ)
  | 47 => (207424673 / 500000000000 : ℝ)
  | 48 => (67926233 / 200000000000 : ℝ)
  | 49 => (69047811 / 250000000000 : ℝ)
  | 50 => (223062647 / 1000000000000 : ℝ)
  | 51 => (178889891 / 1000000000000 : ℝ)
  | 52 => (142433531 / 1000000000000 : ℝ)
  | 53 => (5628591 / 50000000000 : ℝ)
  | 54 => (4414989 / 50000000000 : ℝ)
  | 55 => (3436303 / 50000000000 : ℝ)
  | 56 => (53067967 / 1000000000000 : ℝ)
  | 57 => (40645057 / 1000000000000 : ℝ)
  | 58 => (7717919 / 250000000000 : ℝ)
  | 59 => (5812199 / 250000000000 : ℝ)
  | 60 => (8677743 / 500000000000 : ℝ)
  | 61 => (12840297 / 1000000000000 : ℝ)
  | 62 => (9412799 / 1000000000000 : ℝ)
  | 63 => (3417739 / 500000000000 : ℝ)
  | 64 => (2458067 / 500000000000 : ℝ)
  | 65 => (700179 / 200000000000 : ℝ)
  | 66 => (2467903 / 1000000000000 : ℝ)
  | 67 => (1721713 / 1000000000000 : ℝ)
  | 68 => (1188407 / 1000000000000 : ℝ)
  | 69 => (405691 / 500000000000 : ℝ)
  | 70 => (273901 / 500000000000 : ℝ)
  | 71 => (365627 / 1000000000000 : ℝ)
  | 72 => (120591 / 500000000000 : ℝ)
  | 73 => (157187 / 1000000000000 : ℝ)
  | 74 => (50593 / 500000000000 : ℝ)
  | 75 => (64317 / 1000000000000 : ℝ)
  | 76 => (8071 / 200000000000 : ℝ)
  | 77 => (4997 / 200000000000 : ℝ)
  | 78 => (763 / 50000000000 : ℝ)
  | 79 => (9191 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaJensenBatchSecondLower (b : ℕ) : ℝ :=
  match b with
  | 0 => (21407 / 20000000000 : ℝ)
  | 1 => (3904781 / 500000000000 : ℝ)
  | 2 => (21347403 / 1000000000000 : ℝ)
  | 3 => (41448637 / 1000000000000 : ℝ)
  | 4 => (67761317 / 1000000000000 : ℝ)
  | 5 => (99824291 / 1000000000000 : ℝ)
  | 6 => (17134569 / 125000000000 : ℝ)
  | 7 => (178868303 / 1000000000000 : ℝ)
  | 8 => (112236791 / 500000000000 : ℝ)
  | 9 => (273104221 / 1000000000000 : ℝ)
  | 10 => (8098123 / 25000000000 : ℝ)
  | 11 => (376069137 / 1000000000000 : ℝ)
  | 12 => (428655517 / 1000000000000 : ℝ)
  | 13 => (480804513 / 1000000000000 : ℝ)
  | 14 => (531654877 / 1000000000000 : ℝ)
  | 15 => (3627373 / 6250000000 : ℝ)
  | 16 => (313100749 / 500000000000 : ℝ)
  | 17 => (668406463 / 1000000000000 : ℝ)
  | 18 => (706356849 / 1000000000000 : ℝ)
  | 19 => (369750957 / 500000000000 : ℝ)
  | 20 => (383693387 / 500000000000 : ℝ)
  | 21 => (78965909 / 100000000000 : ℝ)
  | 22 => (403036717 / 500000000000 : ℝ)
  | 23 => (408246629 / 500000000000 : ℝ)
  | 24 => (205222607 / 250000000000 : ℝ)
  | 25 => (819342373 / 1000000000000 : ℝ)
  | 26 => (203006737 / 250000000000 : ℝ)
  | 27 => (799215183 / 1000000000000 : ℝ)
  | 28 => (39063107 / 50000000000 : ℝ)
  | 29 => (758596143 / 1000000000000 : ℝ)
  | 30 => (4573167 / 6250000000 : ℝ)
  | 31 => (701131583 / 1000000000000 : ℝ)
  | 32 => (667443027 / 1000000000000 : ℝ)
  | 33 => (126246829 / 200000000000 : ℝ)
  | 34 => (118621041 / 200000000000 : ℝ)
  | 35 => (276825291 / 500000000000 : ℝ)
  | 36 => (513446561 / 1000000000000 : ℝ)
  | 37 => (118260079 / 250000000000 : ℝ)
  | 38 => (432940311 / 1000000000000 : ℝ)
  | 39 => (393608313 / 1000000000000 : ℝ)
  | 40 => (177726581 / 500000000000 : ℝ)
  | 41 => (79706587 / 250000000000 : ℝ)
  | 42 => (284019417 / 1000000000000 : ℝ)
  | 43 => (251263151 / 1000000000000 : ℝ)
  | 44 => (110364199 / 500000000000 : ℝ)
  | 45 => (192528413 / 1000000000000 : ℝ)
  | 46 => (16672249 / 100000000000 : ℝ)
  | 47 => (3583017 / 25000000000 : ℝ)
  | 48 => (122289317 / 1000000000000 : ℝ)
  | 49 => (12944641 / 125000000000 : ℝ)
  | 50 => (87021653 / 1000000000000 : ℝ)
  | 51 => (3627787 / 50000000000 : ℝ)
  | 52 => (60013901 / 1000000000000 : ℝ)
  | 53 => (9847667 / 200000000000 : ℝ)
  | 54 => (40064467 / 1000000000000 : ℝ)
  | 55 => (3232587 / 100000000000 : ℝ)
  | 56 => (5171703 / 200000000000 : ℝ)
  | 57 => (20504271 / 1000000000000 : ℝ)
  | 58 => (8056839 / 500000000000 : ℝ)
  | 59 => (6273993 / 500000000000 : ℝ)
  | 60 => (9680527 / 1000000000000 : ℝ)
  | 61 => (3698737 / 500000000000 : ℝ)
  | 62 => (559807 / 100000000000 : ℝ)
  | 63 => (4194419 / 1000000000000 : ℝ)
  | 64 => (3110921 / 1000000000000 : ℝ)
  | 65 => (1141727 / 500000000000 : ℝ)
  | 66 => (3239 / 1953125000 : ℝ)
  | 67 => (595691 / 500000000000 : ℝ)
  | 68 => (21161 / 25000000000 : ℝ)
  | 69 => (594573 / 1000000000000 : ℝ)
  | 70 => (16513 / 40000000000 : ℝ)
  | 71 => (56649 / 200000000000 : ℝ)
  | 72 => (47997 / 250000000000 : ℝ)
  | 73 => (128521 / 1000000000000 : ℝ)
  | 74 => (42473 / 500000000000 : ℝ)
  | 75 => (55417 / 1000000000000 : ℝ)
  | 76 => (35673 / 1000000000000 : ℝ)
  | 77 => (5663 / 250000000000 : ℝ)
  | 78 => (1773 / 125000000000 : ℝ)
  | 79 => (1751 / 200000000000 : ℝ)
  | _ => 0

def hpThetaJensenBatchFourthUpper (b : ℕ) : ℝ :=
  match b with
  | 0 => (31 / 250000000000 : ℝ)
  | 1 => (449 / 125000000000 : ℝ)
  | 2 => (4759 / 200000000000 : ℝ)
  | 3 => (86429 / 1000000000000 : ℝ)
  | 4 => (228473 / 1000000000000 : ℝ)
  | 5 => (62069 / 125000000000 : ℝ)
  | 6 => (18897 / 20000000000 : ℝ)
  | 7 => (408161 / 250000000000 : ℝ)
  | 8 => (2621551 / 1000000000000 : ℝ)
  | 9 => (248287 / 62500000000 : ℝ)
  | 10 => (5743177 / 1000000000000 : ℝ)
  | 11 => (798413 / 100000000000 : ℝ)
  | 12 => (2147373 / 200000000000 : ℝ)
  | 13 => (7015411 / 500000000000 : ℝ)
  | 14 => (8940637 / 500000000000 : ℝ)
  | 15 => (22287591 / 1000000000000 : ℝ)
  | 16 => (13616019 / 500000000000 : ℝ)
  | 17 => (16339589 / 500000000000 : ℝ)
  | 18 => (38575903 / 1000000000000 : ℝ)
  | 19 => (22426059 / 500000000000 : ℝ)
  | 20 => (51422063 / 1000000000000 : ℝ)
  | 21 => (46549 / 800000000 : ℝ)
  | 22 => (65033939 / 1000000000000 : ℝ)
  | 23 => (35923043 / 500000000000 : ℝ)
  | 24 => (3924933 / 50000000000 : ℝ)
  | 25 => (16973241 / 200000000000 : ℝ)
  | 26 => (90825531 / 1000000000000 : ℝ)
  | 27 => (48129689 / 500000000000 : ℝ)
  | 28 => (12632493 / 125000000000 : ℝ)
  | 29 => (105132121 / 1000000000000 : ℝ)
  | 30 => (54198163 / 500000000000 : ℝ)
  | 31 => (110790827 / 1000000000000 : ℝ)
  | 32 => (28068367 / 250000000000 : ℝ)
  | 33 => (56411369 / 500000000000 : ℝ)
  | 34 => (878423 / 7812500000 : ℝ)
  | 35 => (111139891 / 1000000000000 : ℝ)
  | 36 => (108967877 / 1000000000000 : ℝ)
  | 37 => (52990039 / 500000000000 : ℝ)
  | 38 => (102250363 / 1000000000000 : ℝ)
  | 39 => (782927 / 8000000000 : ℝ)
  | 40 => (92924061 / 1000000000000 : ℝ)
  | 41 => (87529493 / 1000000000000 : ℝ)
  | 42 => (40895301 / 500000000000 : ℝ)
  | 43 => (37908227 / 500000000000 : ℝ)
  | 44 => (34856847 / 500000000000 : ℝ)
  | 45 => (63583761 / 1000000000000 : ℝ)
  | 46 => (11504093 / 200000000000 : ℝ)
  | 47 => (25803999 / 500000000000 : ℝ)
  | 48 => (5739929 / 125000000000 : ℝ)
  | 49 => (5064463 / 125000000000 : ℝ)
  | 50 => (8861281 / 250000000000 : ℝ)
  | 51 => (3842917 / 125000000000 : ℝ)
  | 52 => (13216867 / 500000000000 : ℝ)
  | 53 => (281603 / 12500000000 : ℝ)
  | 54 => (4757097 / 250000000000 : ℝ)
  | 55 => (15926641 / 1000000000000 : ℝ)
  | 56 => (3301961 / 250000000000 : ℝ)
  | 57 => (271269 / 25000000000 : ℝ)
  | 58 => (8829587 / 1000000000000 : ℝ)
  | 59 => (7115429 / 1000000000000 : ℝ)
  | 60 => (1135527 / 200000000000 : ℝ)
  | 61 => (4484989 / 1000000000000 : ℝ)
  | 62 => (876681 / 250000000000 : ℝ)
  | 63 => (2713337 / 1000000000000 : ℝ)
  | 64 => (259651 / 125000000000 : ℝ)
  | 65 => (786519 / 500000000000 : ℝ)
  | 66 => (589057 / 500000000000 : ℝ)
  | 67 => (436211 / 500000000000 : ℝ)
  | 68 => (7983 / 12500000000 : ℝ)
  | 69 => (28877 / 62500000000 : ℝ)
  | 70 => (330267 / 1000000000000 : ℝ)
  | 71 => (233199 / 1000000000000 : ℝ)
  | 72 => (162607 / 1000000000000 : ℝ)
  | 73 => (5597 / 50000000000 : ℝ)
  | 74 => (38029 / 500000000000 : ℝ)
  | 75 => (50991 / 1000000000000 : ℝ)
  | 76 => (33721 / 1000000000000 : ℝ)
  | 77 => (2199 / 100000000000 : ℝ)
  | 78 => (14137 / 1000000000000 : ℝ)
  | 79 => (2239 / 250000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Twenty rational terms are verified for each of the three moment orders.
theorem hpThetaJensenCellsBatch000_finiteIntegral_bounds :
    (∫ u : ℝ in Set.Ioo (0 / 80 : ℝ) ((0 + 1) / 80 : ℝ), u ^ 0 * hpRiemannThetaDifferentialKernel
      u) ≤
        hpThetaJensenBatchZeroUpper 0 ∧
    hpThetaJensenBatchSecondLower 0 ≤
        (∫ u : ℝ in Set.Ioo (0 / 80 : ℝ) ((0 + 1) / 80 : ℝ), u ^ 2 *
          hpRiemannThetaDifferentialKernel u) ∧
    (∫ u : ℝ in Set.Ioo (0 / 80 : ℝ) ((0 + 1) / 80 : ℝ), u ^ 4 * hpRiemannThetaDifferentialKernel
      u) ≤
        hpThetaJensenBatchFourthUpper 0 := by
  have hs (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
      (∑ j ∈ Finset.range 20, ∫ u : ℝ in Set.Ioo (((0 : ℝ) + (j : ℝ)) / 1600) (((0 : ℝ) + (j : ℝ)
        + 1) / 1600),
        u ^ m * hpRiemannThetaDifferentialKernel u) =
      ∫ u : ℝ in Set.Ioo (0 / 80 : ℝ) ((0 + 1) / 80 : ℝ), u ^ m * hpRiemannThetaDifferentialKernel
        u := by
    have h := hpThetaJensen_batchCellIntegral_sum m hm 0
    have hc : ∀ j : ℕ,
        Set.Ioo (((0 : ℝ) + (j : ℝ)) / 1600) (((0 : ℝ) + (j : ℝ) + 1) / 1600) =
          Set.Ioo ((0 : ℝ) / 80 + (j : ℝ) / 1600)
            ((0 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600) := by
      intro j
      have hl : (((0 : ℝ) + (j : ℝ)) / 1600) = (0 : ℝ) / 80 + (j : ℝ) / 1600 := by ring
      have hr : (((0 : ℝ) + (j : ℝ) + 1) / 1600) = (0 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600 := by
        push_cast
        ring
      rw [hl, hr]
    simp_rw [hc]
    simpa only [Nat.cast_zero] using h
  have h0 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((0 : ℝ) + (j : ℝ)) / 1600) (((0 : ℝ) + (j : ℝ) + 1) / 1600), u ^ 0 *
        hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((0 : ℝ) + (j : ℝ) + 1) / 1600) ^ 0 *
        hpThetaJensenCellsBatch000Upper j * ((((0 : ℝ) + (j : ℝ) + 1) / 1600) - (((0 : ℝ) + (j :
        ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch000_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 0
      (Or.inl rfl)).2
  have h2 : (∑ j ∈ Finset.range 20, (((0 : ℝ) + (j : ℝ)) / 1600) ^ 2 *
    hpThetaJensenCellsBatch000Lower j * ((((0 : ℝ) + (j : ℝ) + 1) / 1600) - (((0 : ℝ) + (j : ℝ)) /
    1600))) ≤
      ∑ j ∈ Finset.range 20,
        ∫ u : ℝ in Set.Ioo (((0 : ℝ) + (j : ℝ)) / 1600) (((0 : ℝ) + (j : ℝ) + 1) / 1600), u ^ 2 *
          hpRiemannThetaDifferentialKernel u := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch000_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 2
      (Or.inr (Or.inl rfl))).1
  have h4 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((0 : ℝ) + (j : ℝ)) / 1600) (((0 : ℝ) + (j : ℝ) + 1) / 1600), u ^ 4 *
        hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((0 : ℝ) + (j : ℝ) + 1) / 1600) ^ 4 *
        hpThetaJensenCellsBatch000Upper j * ((((0 : ℝ) + (j : ℝ) + 1) / 1600) - (((0 : ℝ) + (j :
        ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch000_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 4
      (Or.inr (Or.inr rfl))).2
  rw [hs 0 (Or.inl rfl)] at h0
  rw [hs 2 (Or.inr (Or.inl rfl))] at h2
  rw [hs 4 (Or.inr (Or.inr rfl))] at h4
  norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch000Lower,
    hpThetaJensenCellsBatch000Upper] at h0 h2 h4
  norm_num [hpThetaJensenBatchZeroUpper, hpThetaJensenBatchSecondLower,
    hpThetaJensenBatchFourthUpper]
  exact ⟨le_trans h0 (by norm_num), le_trans (by norm_num) h2,
    le_trans h4 (by norm_num)⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Twenty rational terms are verified for each of the three moment orders.
theorem hpThetaJensenCellsBatch001_finiteIntegral_bounds :
    (∫ u : ℝ in Set.Ioo (1 / 80 : ℝ) ((1 + 1) / 80 : ℝ), u ^ 0 * hpRiemannThetaDifferentialKernel
      u) ≤
        hpThetaJensenBatchZeroUpper 1 ∧
    hpThetaJensenBatchSecondLower 1 ≤
        (∫ u : ℝ in Set.Ioo (1 / 80 : ℝ) ((1 + 1) / 80 : ℝ), u ^ 2 *
          hpRiemannThetaDifferentialKernel u) ∧
    (∫ u : ℝ in Set.Ioo (1 / 80 : ℝ) ((1 + 1) / 80 : ℝ), u ^ 4 * hpRiemannThetaDifferentialKernel
      u) ≤
        hpThetaJensenBatchFourthUpper 1 := by
  have hs (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
      (∑ j ∈ Finset.range 20, ∫ u : ℝ in Set.Ioo (((20 : ℝ) + (j : ℝ)) / 1600) (((20 : ℝ) + (j :
        ℝ) + 1) / 1600),
        u ^ m * hpRiemannThetaDifferentialKernel u) =
      ∫ u : ℝ in Set.Ioo (1 / 80 : ℝ) ((1 + 1) / 80 : ℝ), u ^ m * hpRiemannThetaDifferentialKernel
        u := by
    have h := hpThetaJensen_batchCellIntegral_sum m hm 1
    have hc : ∀ j : ℕ,
        Set.Ioo (((20 : ℝ) + (j : ℝ)) / 1600) (((20 : ℝ) + (j : ℝ) + 1) / 1600) =
          Set.Ioo ((1 : ℝ) / 80 + (j : ℝ) / 1600)
            ((1 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600) := by
      intro j
      have hl : (((20 : ℝ) + (j : ℝ)) / 1600) = (1 : ℝ) / 80 + (j : ℝ) / 1600 := by ring
      have hr : (((20 : ℝ) + (j : ℝ) + 1) / 1600) = (1 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600 := by
        push_cast
        ring
      rw [hl, hr]
    simp_rw [hc]
    simpa only [Nat.cast_one] using h
  have h0 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((20 : ℝ) + (j : ℝ)) / 1600) (((20 : ℝ) + (j : ℝ) + 1) / 1600), u ^ 0 *
        hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((20 : ℝ) + (j : ℝ) + 1) / 1600) ^ 0 *
        hpThetaJensenCellsBatch001Upper j * ((((20 : ℝ) + (j : ℝ) + 1) / 1600) - (((20 : ℝ) + (j :
        ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch001_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 0
      (Or.inl rfl)).2
  have h2 : (∑ j ∈ Finset.range 20, (((20 : ℝ) + (j : ℝ)) / 1600) ^ 2 *
    hpThetaJensenCellsBatch001Lower j * ((((20 : ℝ) + (j : ℝ) + 1) / 1600) - (((20 : ℝ) + (j : ℝ))
    / 1600))) ≤
      ∑ j ∈ Finset.range 20,
        ∫ u : ℝ in Set.Ioo (((20 : ℝ) + (j : ℝ)) / 1600) (((20 : ℝ) + (j : ℝ) + 1) / 1600), u ^ 2
          * hpRiemannThetaDifferentialKernel u := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch001_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 2
      (Or.inr (Or.inl rfl))).1
  have h4 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((20 : ℝ) + (j : ℝ)) / 1600) (((20 : ℝ) + (j : ℝ) + 1) / 1600), u ^ 4 *
        hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((20 : ℝ) + (j : ℝ) + 1) / 1600) ^ 4 *
        hpThetaJensenCellsBatch001Upper j * ((((20 : ℝ) + (j : ℝ) + 1) / 1600) - (((20 : ℝ) + (j :
        ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch001_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 4
      (Or.inr (Or.inr rfl))).2
  rw [hs 0 (Or.inl rfl)] at h0
  rw [hs 2 (Or.inr (Or.inl rfl))] at h2
  rw [hs 4 (Or.inr (Or.inr rfl))] at h4
  norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch001Lower,
    hpThetaJensenCellsBatch001Upper] at h0 h2 h4
  norm_num [hpThetaJensenBatchZeroUpper, hpThetaJensenBatchSecondLower,
    hpThetaJensenBatchFourthUpper]
  exact ⟨le_trans h0 (by norm_num), le_trans (by norm_num) h2,
    le_trans h4 (by norm_num)⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Twenty rational terms are verified for each of the three moment orders.
theorem hpThetaJensenCellsBatch002_finiteIntegral_bounds :
    (∫ u : ℝ in Set.Ioo (2 / 80 : ℝ) ((2 + 1) / 80 : ℝ), u ^ 0 * hpRiemannThetaDifferentialKernel
      u) ≤
        hpThetaJensenBatchZeroUpper 2 ∧
    hpThetaJensenBatchSecondLower 2 ≤
        (∫ u : ℝ in Set.Ioo (2 / 80 : ℝ) ((2 + 1) / 80 : ℝ), u ^ 2 *
          hpRiemannThetaDifferentialKernel u) ∧
    (∫ u : ℝ in Set.Ioo (2 / 80 : ℝ) ((2 + 1) / 80 : ℝ), u ^ 4 * hpRiemannThetaDifferentialKernel
      u) ≤
        hpThetaJensenBatchFourthUpper 2 := by
  have hs (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
      (∑ j ∈ Finset.range 20, ∫ u : ℝ in Set.Ioo (((40 : ℝ) + (j : ℝ)) / 1600) (((40 : ℝ) + (j :
        ℝ) + 1) / 1600),
        u ^ m * hpRiemannThetaDifferentialKernel u) =
      ∫ u : ℝ in Set.Ioo (2 / 80 : ℝ) ((2 + 1) / 80 : ℝ), u ^ m * hpRiemannThetaDifferentialKernel
        u := by
    have h := hpThetaJensen_batchCellIntegral_sum m hm 2
    have hc : ∀ j : ℕ,
        Set.Ioo (((40 : ℝ) + (j : ℝ)) / 1600) (((40 : ℝ) + (j : ℝ) + 1) / 1600) =
          Set.Ioo ((2 : ℝ) / 80 + (j : ℝ) / 1600)
            ((2 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600) := by
      intro j
      have hl : (((40 : ℝ) + (j : ℝ)) / 1600) = (2 : ℝ) / 80 + (j : ℝ) / 1600 := by ring
      have hr : (((40 : ℝ) + (j : ℝ) + 1) / 1600) = (2 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600 := by
        push_cast
        ring
      rw [hl, hr]
    simp_rw [hc]
    exact h
  have h0 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((40 : ℝ) + (j : ℝ)) / 1600) (((40 : ℝ) + (j : ℝ) + 1) / 1600), u ^ 0 *
        hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((40 : ℝ) + (j : ℝ) + 1) / 1600) ^ 0 *
        hpThetaJensenCellsBatch002Upper j * ((((40 : ℝ) + (j : ℝ) + 1) / 1600) - (((40 : ℝ) + (j :
        ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch002_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 0
      (Or.inl rfl)).2
  have h2 : (∑ j ∈ Finset.range 20, (((40 : ℝ) + (j : ℝ)) / 1600) ^ 2 *
    hpThetaJensenCellsBatch002Lower j * ((((40 : ℝ) + (j : ℝ) + 1) / 1600) - (((40 : ℝ) + (j : ℝ))
    / 1600))) ≤
      ∑ j ∈ Finset.range 20,
        ∫ u : ℝ in Set.Ioo (((40 : ℝ) + (j : ℝ)) / 1600) (((40 : ℝ) + (j : ℝ) + 1) / 1600), u ^ 2
          * hpRiemannThetaDifferentialKernel u := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch002_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 2
      (Or.inr (Or.inl rfl))).1
  have h4 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((40 : ℝ) + (j : ℝ)) / 1600) (((40 : ℝ) + (j : ℝ) + 1) / 1600), u ^ 4 *
        hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((40 : ℝ) + (j : ℝ) + 1) / 1600) ^ 4 *
        hpThetaJensenCellsBatch002Upper j * ((((40 : ℝ) + (j : ℝ) + 1) / 1600) - (((40 : ℝ) + (j :
        ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch002_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 4
      (Or.inr (Or.inr rfl))).2
  rw [hs 0 (Or.inl rfl)] at h0
  rw [hs 2 (Or.inr (Or.inl rfl))] at h2
  rw [hs 4 (Or.inr (Or.inr rfl))] at h4
  norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch002Lower,
    hpThetaJensenCellsBatch002Upper] at h0 h2 h4
  norm_num [hpThetaJensenBatchZeroUpper, hpThetaJensenBatchSecondLower,
    hpThetaJensenBatchFourthUpper]
  exact ⟨le_trans h0 (by norm_num), le_trans (by norm_num) h2,
    le_trans h4 (by norm_num)⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Twenty rational terms are verified for each of the three moment orders.
theorem hpThetaJensenCellsBatch003_finiteIntegral_bounds :
    (∫ u : ℝ in Set.Ioo (3 / 80 : ℝ) ((3 + 1) / 80 : ℝ), u ^ 0 * hpRiemannThetaDifferentialKernel
      u) ≤
        hpThetaJensenBatchZeroUpper 3 ∧
    hpThetaJensenBatchSecondLower 3 ≤
        (∫ u : ℝ in Set.Ioo (3 / 80 : ℝ) ((3 + 1) / 80 : ℝ), u ^ 2 *
          hpRiemannThetaDifferentialKernel u) ∧
    (∫ u : ℝ in Set.Ioo (3 / 80 : ℝ) ((3 + 1) / 80 : ℝ), u ^ 4 * hpRiemannThetaDifferentialKernel
      u) ≤
        hpThetaJensenBatchFourthUpper 3 := by
  have hs (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
      (∑ j ∈ Finset.range 20, ∫ u : ℝ in Set.Ioo (((60 : ℝ) + (j : ℝ)) / 1600) (((60 : ℝ) + (j :
        ℝ) + 1) / 1600),
        u ^ m * hpRiemannThetaDifferentialKernel u) =
      ∫ u : ℝ in Set.Ioo (3 / 80 : ℝ) ((3 + 1) / 80 : ℝ), u ^ m * hpRiemannThetaDifferentialKernel
        u := by
    have h := hpThetaJensen_batchCellIntegral_sum m hm 3
    have hc : ∀ j : ℕ,
        Set.Ioo (((60 : ℝ) + (j : ℝ)) / 1600) (((60 : ℝ) + (j : ℝ) + 1) / 1600) =
          Set.Ioo ((3 : ℝ) / 80 + (j : ℝ) / 1600)
            ((3 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600) := by
      intro j
      have hl : (((60 : ℝ) + (j : ℝ)) / 1600) = (3 : ℝ) / 80 + (j : ℝ) / 1600 := by ring
      have hr : (((60 : ℝ) + (j : ℝ) + 1) / 1600) = (3 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600 := by
        push_cast
        ring
      rw [hl, hr]
    simp_rw [hc]
    exact h
  have h0 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((60 : ℝ) + (j : ℝ)) / 1600) (((60 : ℝ) + (j : ℝ) + 1) / 1600), u ^ 0 *
        hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((60 : ℝ) + (j : ℝ) + 1) / 1600) ^ 0 *
        hpThetaJensenCellsBatch003Upper j * ((((60 : ℝ) + (j : ℝ) + 1) / 1600) - (((60 : ℝ) + (j :
        ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch003_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 0
      (Or.inl rfl)).2
  have h2 : (∑ j ∈ Finset.range 20, (((60 : ℝ) + (j : ℝ)) / 1600) ^ 2 *
    hpThetaJensenCellsBatch003Lower j * ((((60 : ℝ) + (j : ℝ) + 1) / 1600) - (((60 : ℝ) + (j : ℝ))
    / 1600))) ≤
      ∑ j ∈ Finset.range 20,
        ∫ u : ℝ in Set.Ioo (((60 : ℝ) + (j : ℝ)) / 1600) (((60 : ℝ) + (j : ℝ) + 1) / 1600), u ^ 2
          * hpRiemannThetaDifferentialKernel u := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch003_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 2
      (Or.inr (Or.inl rfl))).1
  have h4 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((60 : ℝ) + (j : ℝ)) / 1600) (((60 : ℝ) + (j : ℝ) + 1) / 1600), u ^ 4 *
        hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((60 : ℝ) + (j : ℝ) + 1) / 1600) ^ 4 *
        hpThetaJensenCellsBatch003Upper j * ((((60 : ℝ) + (j : ℝ) + 1) / 1600) - (((60 : ℝ) + (j :
        ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch003_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 4
      (Or.inr (Or.inr rfl))).2
  rw [hs 0 (Or.inl rfl)] at h0
  rw [hs 2 (Or.inr (Or.inl rfl))] at h2
  rw [hs 4 (Or.inr (Or.inr rfl))] at h4
  norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch003Lower,
    hpThetaJensenCellsBatch003Upper] at h0 h2 h4
  norm_num [hpThetaJensenBatchZeroUpper, hpThetaJensenBatchSecondLower,
    hpThetaJensenBatchFourthUpper]
  exact ⟨le_trans h0 (by norm_num), le_trans (by norm_num) h2,
    le_trans h4 (by norm_num)⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Twenty rational terms are verified for each of the three moment orders.
theorem hpThetaJensenCellsBatch004_finiteIntegral_bounds :
    (∫ u : ℝ in Set.Ioo (4 / 80 : ℝ) ((4 + 1) / 80 : ℝ), u ^ 0 * hpRiemannThetaDifferentialKernel
      u) ≤
        hpThetaJensenBatchZeroUpper 4 ∧
    hpThetaJensenBatchSecondLower 4 ≤
        (∫ u : ℝ in Set.Ioo (4 / 80 : ℝ) ((4 + 1) / 80 : ℝ), u ^ 2 *
          hpRiemannThetaDifferentialKernel u) ∧
    (∫ u : ℝ in Set.Ioo (4 / 80 : ℝ) ((4 + 1) / 80 : ℝ), u ^ 4 * hpRiemannThetaDifferentialKernel
      u) ≤
        hpThetaJensenBatchFourthUpper 4 := by
  have hs (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
      (∑ j ∈ Finset.range 20, ∫ u : ℝ in Set.Ioo (((80 : ℝ) + (j : ℝ)) / 1600) (((80 : ℝ) + (j :
        ℝ) + 1) / 1600),
        u ^ m * hpRiemannThetaDifferentialKernel u) =
      ∫ u : ℝ in Set.Ioo (4 / 80 : ℝ) ((4 + 1) / 80 : ℝ), u ^ m * hpRiemannThetaDifferentialKernel
        u := by
    have h := hpThetaJensen_batchCellIntegral_sum m hm 4
    have hc : ∀ j : ℕ,
        Set.Ioo (((80 : ℝ) + (j : ℝ)) / 1600) (((80 : ℝ) + (j : ℝ) + 1) / 1600) =
          Set.Ioo ((4 : ℝ) / 80 + (j : ℝ) / 1600)
            ((4 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600) := by
      intro j
      have hl : (((80 : ℝ) + (j : ℝ)) / 1600) = (4 : ℝ) / 80 + (j : ℝ) / 1600 := by ring
      have hr : (((80 : ℝ) + (j : ℝ) + 1) / 1600) = (4 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600 := by
        push_cast
        ring
      rw [hl, hr]
    simp_rw [hc]
    exact h
  have h0 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((80 : ℝ) + (j : ℝ)) / 1600) (((80 : ℝ) + (j : ℝ) + 1) / 1600), u ^ 0 *
        hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((80 : ℝ) + (j : ℝ) + 1) / 1600) ^ 0 *
        hpThetaJensenCellsBatch004Upper j * ((((80 : ℝ) + (j : ℝ) + 1) / 1600) - (((80 : ℝ) + (j :
        ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch004_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 0
      (Or.inl rfl)).2
  have h2 : (∑ j ∈ Finset.range 20, (((80 : ℝ) + (j : ℝ)) / 1600) ^ 2 *
    hpThetaJensenCellsBatch004Lower j * ((((80 : ℝ) + (j : ℝ) + 1) / 1600) - (((80 : ℝ) + (j : ℝ))
    / 1600))) ≤
      ∑ j ∈ Finset.range 20,
        ∫ u : ℝ in Set.Ioo (((80 : ℝ) + (j : ℝ)) / 1600) (((80 : ℝ) + (j : ℝ) + 1) / 1600), u ^ 2
          * hpRiemannThetaDifferentialKernel u := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch004_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 2
      (Or.inr (Or.inl rfl))).1
  have h4 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((80 : ℝ) + (j : ℝ)) / 1600) (((80 : ℝ) + (j : ℝ) + 1) / 1600), u ^ 4 *
        hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((80 : ℝ) + (j : ℝ) + 1) / 1600) ^ 4 *
        hpThetaJensenCellsBatch004Upper j * ((((80 : ℝ) + (j : ℝ) + 1) / 1600) - (((80 : ℝ) + (j :
        ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch004_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 4
      (Or.inr (Or.inr rfl))).2
  rw [hs 0 (Or.inl rfl)] at h0
  rw [hs 2 (Or.inr (Or.inl rfl))] at h2
  rw [hs 4 (Or.inr (Or.inr rfl))] at h4
  norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch004Lower,
    hpThetaJensenCellsBatch004Upper] at h0 h2 h4
  norm_num [hpThetaJensenBatchZeroUpper, hpThetaJensenBatchSecondLower,
    hpThetaJensenBatchFourthUpper]
  exact ⟨le_trans h0 (by norm_num), le_trans (by norm_num) h2,
    le_trans h4 (by norm_num)⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Twenty rational terms are verified for each of the three moment orders.
theorem hpThetaJensenCellsBatch005_finiteIntegral_bounds :
    (∫ u : ℝ in Set.Ioo (5 / 80 : ℝ) ((5 + 1) / 80 : ℝ), u ^ 0 * hpRiemannThetaDifferentialKernel
      u) ≤
        hpThetaJensenBatchZeroUpper 5 ∧
    hpThetaJensenBatchSecondLower 5 ≤
        (∫ u : ℝ in Set.Ioo (5 / 80 : ℝ) ((5 + 1) / 80 : ℝ), u ^ 2 *
          hpRiemannThetaDifferentialKernel u) ∧
    (∫ u : ℝ in Set.Ioo (5 / 80 : ℝ) ((5 + 1) / 80 : ℝ), u ^ 4 * hpRiemannThetaDifferentialKernel
      u) ≤
        hpThetaJensenBatchFourthUpper 5 := by
  have hs (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
      (∑ j ∈ Finset.range 20, ∫ u : ℝ in Set.Ioo (((100 : ℝ) + (j : ℝ)) / 1600) (((100 : ℝ) + (j :
        ℝ) + 1) / 1600),
        u ^ m * hpRiemannThetaDifferentialKernel u) =
      ∫ u : ℝ in Set.Ioo (5 / 80 : ℝ) ((5 + 1) / 80 : ℝ), u ^ m * hpRiemannThetaDifferentialKernel
        u := by
    have h := hpThetaJensen_batchCellIntegral_sum m hm 5
    have hc : ∀ j : ℕ,
        Set.Ioo (((100 : ℝ) + (j : ℝ)) / 1600) (((100 : ℝ) + (j : ℝ) + 1) / 1600) =
          Set.Ioo ((5 : ℝ) / 80 + (j : ℝ) / 1600)
            ((5 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600) := by
      intro j
      have hl : (((100 : ℝ) + (j : ℝ)) / 1600) = (5 : ℝ) / 80 + (j : ℝ) / 1600 := by ring
      have hr : (((100 : ℝ) + (j : ℝ) + 1) / 1600) = (5 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600 := by
        push_cast
        ring
      rw [hl, hr]
    simp_rw [hc]
    exact h
  have h0 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((100 : ℝ) + (j : ℝ)) / 1600) (((100 : ℝ) + (j : ℝ) + 1) / 1600), u ^ 0
        * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((100 : ℝ) + (j : ℝ) + 1) / 1600) ^ 0 *
        hpThetaJensenCellsBatch005Upper j * ((((100 : ℝ) + (j : ℝ) + 1) / 1600) - (((100 : ℝ) + (j
        : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch005_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 0
      (Or.inl rfl)).2
  have h2 : (∑ j ∈ Finset.range 20, (((100 : ℝ) + (j : ℝ)) / 1600) ^ 2 *
    hpThetaJensenCellsBatch005Lower j * ((((100 : ℝ) + (j : ℝ) + 1) / 1600) - (((100 : ℝ) + (j :
    ℝ)) / 1600))) ≤
      ∑ j ∈ Finset.range 20,
        ∫ u : ℝ in Set.Ioo (((100 : ℝ) + (j : ℝ)) / 1600) (((100 : ℝ) + (j : ℝ) + 1) / 1600), u ^
          2 * hpRiemannThetaDifferentialKernel u := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch005_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 2
      (Or.inr (Or.inl rfl))).1
  have h4 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((100 : ℝ) + (j : ℝ)) / 1600) (((100 : ℝ) + (j : ℝ) + 1) / 1600), u ^ 4
        * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((100 : ℝ) + (j : ℝ) + 1) / 1600) ^ 4 *
        hpThetaJensenCellsBatch005Upper j * ((((100 : ℝ) + (j : ℝ) + 1) / 1600) - (((100 : ℝ) + (j
        : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch005_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 4
      (Or.inr (Or.inr rfl))).2
  rw [hs 0 (Or.inl rfl)] at h0
  rw [hs 2 (Or.inr (Or.inl rfl))] at h2
  rw [hs 4 (Or.inr (Or.inr rfl))] at h4
  norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch005Lower,
    hpThetaJensenCellsBatch005Upper] at h0 h2 h4
  norm_num [hpThetaJensenBatchZeroUpper, hpThetaJensenBatchSecondLower,
    hpThetaJensenBatchFourthUpper]
  exact ⟨le_trans h0 (by norm_num), le_trans (by norm_num) h2,
    le_trans h4 (by norm_num)⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Twenty rational terms are verified for each of the three moment orders.
theorem hpThetaJensenCellsBatch006_finiteIntegral_bounds :
    (∫ u : ℝ in Set.Ioo (6 / 80 : ℝ) ((6 + 1) / 80 : ℝ), u ^ 0 * hpRiemannThetaDifferentialKernel
      u) ≤
        hpThetaJensenBatchZeroUpper 6 ∧
    hpThetaJensenBatchSecondLower 6 ≤
        (∫ u : ℝ in Set.Ioo (6 / 80 : ℝ) ((6 + 1) / 80 : ℝ), u ^ 2 *
          hpRiemannThetaDifferentialKernel u) ∧
    (∫ u : ℝ in Set.Ioo (6 / 80 : ℝ) ((6 + 1) / 80 : ℝ), u ^ 4 * hpRiemannThetaDifferentialKernel
      u) ≤
        hpThetaJensenBatchFourthUpper 6 := by
  have hs (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
      (∑ j ∈ Finset.range 20, ∫ u : ℝ in Set.Ioo (((120 : ℝ) + (j : ℝ)) / 1600) (((120 : ℝ) + (j :
        ℝ) + 1) / 1600),
        u ^ m * hpRiemannThetaDifferentialKernel u) =
      ∫ u : ℝ in Set.Ioo (6 / 80 : ℝ) ((6 + 1) / 80 : ℝ), u ^ m * hpRiemannThetaDifferentialKernel
        u := by
    have h := hpThetaJensen_batchCellIntegral_sum m hm 6
    have hc : ∀ j : ℕ,
        Set.Ioo (((120 : ℝ) + (j : ℝ)) / 1600) (((120 : ℝ) + (j : ℝ) + 1) / 1600) =
          Set.Ioo ((6 : ℝ) / 80 + (j : ℝ) / 1600)
            ((6 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600) := by
      intro j
      have hl : (((120 : ℝ) + (j : ℝ)) / 1600) = (6 : ℝ) / 80 + (j : ℝ) / 1600 := by ring
      have hr : (((120 : ℝ) + (j : ℝ) + 1) / 1600) = (6 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600 := by
        push_cast
        ring
      rw [hl, hr]
    simp_rw [hc]
    exact h
  have h0 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((120 : ℝ) + (j : ℝ)) / 1600) (((120 : ℝ) + (j : ℝ) + 1) / 1600), u ^ 0
        * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((120 : ℝ) + (j : ℝ) + 1) / 1600) ^ 0 *
        hpThetaJensenCellsBatch006Upper j * ((((120 : ℝ) + (j : ℝ) + 1) / 1600) - (((120 : ℝ) + (j
        : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch006_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 0
      (Or.inl rfl)).2
  have h2 : (∑ j ∈ Finset.range 20, (((120 : ℝ) + (j : ℝ)) / 1600) ^ 2 *
    hpThetaJensenCellsBatch006Lower j * ((((120 : ℝ) + (j : ℝ) + 1) / 1600) - (((120 : ℝ) + (j :
    ℝ)) / 1600))) ≤
      ∑ j ∈ Finset.range 20,
        ∫ u : ℝ in Set.Ioo (((120 : ℝ) + (j : ℝ)) / 1600) (((120 : ℝ) + (j : ℝ) + 1) / 1600), u ^
          2 * hpRiemannThetaDifferentialKernel u := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch006_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 2
      (Or.inr (Or.inl rfl))).1
  have h4 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((120 : ℝ) + (j : ℝ)) / 1600) (((120 : ℝ) + (j : ℝ) + 1) / 1600), u ^ 4
        * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((120 : ℝ) + (j : ℝ) + 1) / 1600) ^ 4 *
        hpThetaJensenCellsBatch006Upper j * ((((120 : ℝ) + (j : ℝ) + 1) / 1600) - (((120 : ℝ) + (j
        : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch006_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 4
      (Or.inr (Or.inr rfl))).2
  rw [hs 0 (Or.inl rfl)] at h0
  rw [hs 2 (Or.inr (Or.inl rfl))] at h2
  rw [hs 4 (Or.inr (Or.inr rfl))] at h4
  norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch006Lower,
    hpThetaJensenCellsBatch006Upper] at h0 h2 h4
  norm_num [hpThetaJensenBatchZeroUpper, hpThetaJensenBatchSecondLower,
    hpThetaJensenBatchFourthUpper]
  exact ⟨le_trans h0 (by norm_num), le_trans (by norm_num) h2,
    le_trans h4 (by norm_num)⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Twenty rational terms are verified for each of the three moment orders.
theorem hpThetaJensenCellsBatch007_finiteIntegral_bounds :
    (∫ u : ℝ in Set.Ioo (7 / 80 : ℝ) ((7 + 1) / 80 : ℝ), u ^ 0 * hpRiemannThetaDifferentialKernel
      u) ≤
        hpThetaJensenBatchZeroUpper 7 ∧
    hpThetaJensenBatchSecondLower 7 ≤
        (∫ u : ℝ in Set.Ioo (7 / 80 : ℝ) ((7 + 1) / 80 : ℝ), u ^ 2 *
          hpRiemannThetaDifferentialKernel u) ∧
    (∫ u : ℝ in Set.Ioo (7 / 80 : ℝ) ((7 + 1) / 80 : ℝ), u ^ 4 * hpRiemannThetaDifferentialKernel
      u) ≤
        hpThetaJensenBatchFourthUpper 7 := by
  have hs (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
      (∑ j ∈ Finset.range 20, ∫ u : ℝ in Set.Ioo (((140 : ℝ) + (j : ℝ)) / 1600) (((140 : ℝ) + (j :
        ℝ) + 1) / 1600),
        u ^ m * hpRiemannThetaDifferentialKernel u) =
      ∫ u : ℝ in Set.Ioo (7 / 80 : ℝ) ((7 + 1) / 80 : ℝ), u ^ m * hpRiemannThetaDifferentialKernel
        u := by
    have h := hpThetaJensen_batchCellIntegral_sum m hm 7
    have hc : ∀ j : ℕ,
        Set.Ioo (((140 : ℝ) + (j : ℝ)) / 1600) (((140 : ℝ) + (j : ℝ) + 1) / 1600) =
          Set.Ioo ((7 : ℝ) / 80 + (j : ℝ) / 1600)
            ((7 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600) := by
      intro j
      have hl : (((140 : ℝ) + (j : ℝ)) / 1600) = (7 : ℝ) / 80 + (j : ℝ) / 1600 := by ring
      have hr : (((140 : ℝ) + (j : ℝ) + 1) / 1600) = (7 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600 := by
        push_cast
        ring
      rw [hl, hr]
    simp_rw [hc]
    exact h
  have h0 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((140 : ℝ) + (j : ℝ)) / 1600) (((140 : ℝ) + (j : ℝ) + 1) / 1600), u ^ 0
        * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((140 : ℝ) + (j : ℝ) + 1) / 1600) ^ 0 *
        hpThetaJensenCellsBatch007Upper j * ((((140 : ℝ) + (j : ℝ) + 1) / 1600) - (((140 : ℝ) + (j
        : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch007_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 0
      (Or.inl rfl)).2
  have h2 : (∑ j ∈ Finset.range 20, (((140 : ℝ) + (j : ℝ)) / 1600) ^ 2 *
    hpThetaJensenCellsBatch007Lower j * ((((140 : ℝ) + (j : ℝ) + 1) / 1600) - (((140 : ℝ) + (j :
    ℝ)) / 1600))) ≤
      ∑ j ∈ Finset.range 20,
        ∫ u : ℝ in Set.Ioo (((140 : ℝ) + (j : ℝ)) / 1600) (((140 : ℝ) + (j : ℝ) + 1) / 1600), u ^
          2 * hpRiemannThetaDifferentialKernel u := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch007_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 2
      (Or.inr (Or.inl rfl))).1
  have h4 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((140 : ℝ) + (j : ℝ)) / 1600) (((140 : ℝ) + (j : ℝ) + 1) / 1600), u ^ 4
        * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((140 : ℝ) + (j : ℝ) + 1) / 1600) ^ 4 *
        hpThetaJensenCellsBatch007Upper j * ((((140 : ℝ) + (j : ℝ) + 1) / 1600) - (((140 : ℝ) + (j
        : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch007_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 4
      (Or.inr (Or.inr rfl))).2
  rw [hs 0 (Or.inl rfl)] at h0
  rw [hs 2 (Or.inr (Or.inl rfl))] at h2
  rw [hs 4 (Or.inr (Or.inr rfl))] at h4
  norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch007Lower,
    hpThetaJensenCellsBatch007Upper] at h0 h2 h4
  norm_num [hpThetaJensenBatchZeroUpper, hpThetaJensenBatchSecondLower,
    hpThetaJensenBatchFourthUpper]
  exact ⟨le_trans h0 (by norm_num), le_trans (by norm_num) h2,
    le_trans h4 (by norm_num)⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Twenty rational terms are verified for each of the three moment orders.
theorem hpThetaJensenCellsBatch008_finiteIntegral_bounds :
    (∫ u : ℝ in Set.Ioo (8 / 80 : ℝ) ((8 + 1) / 80 : ℝ), u ^ 0 * hpRiemannThetaDifferentialKernel
      u) ≤
        hpThetaJensenBatchZeroUpper 8 ∧
    hpThetaJensenBatchSecondLower 8 ≤
        (∫ u : ℝ in Set.Ioo (8 / 80 : ℝ) ((8 + 1) / 80 : ℝ), u ^ 2 *
          hpRiemannThetaDifferentialKernel u) ∧
    (∫ u : ℝ in Set.Ioo (8 / 80 : ℝ) ((8 + 1) / 80 : ℝ), u ^ 4 * hpRiemannThetaDifferentialKernel
      u) ≤
        hpThetaJensenBatchFourthUpper 8 := by
  have hs (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
      (∑ j ∈ Finset.range 20, ∫ u : ℝ in Set.Ioo (((160 : ℝ) + (j : ℝ)) / 1600) (((160 : ℝ) + (j :
        ℝ) + 1) / 1600),
        u ^ m * hpRiemannThetaDifferentialKernel u) =
      ∫ u : ℝ in Set.Ioo (8 / 80 : ℝ) ((8 + 1) / 80 : ℝ), u ^ m * hpRiemannThetaDifferentialKernel
        u := by
    have h := hpThetaJensen_batchCellIntegral_sum m hm 8
    have hc : ∀ j : ℕ,
        Set.Ioo (((160 : ℝ) + (j : ℝ)) / 1600) (((160 : ℝ) + (j : ℝ) + 1) / 1600) =
          Set.Ioo ((8 : ℝ) / 80 + (j : ℝ) / 1600)
            ((8 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600) := by
      intro j
      have hl : (((160 : ℝ) + (j : ℝ)) / 1600) = (8 : ℝ) / 80 + (j : ℝ) / 1600 := by ring
      have hr : (((160 : ℝ) + (j : ℝ) + 1) / 1600) = (8 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600 := by
        push_cast
        ring
      rw [hl, hr]
    simp_rw [hc]
    exact h
  have h0 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((160 : ℝ) + (j : ℝ)) / 1600) (((160 : ℝ) + (j : ℝ) + 1) / 1600), u ^ 0
        * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((160 : ℝ) + (j : ℝ) + 1) / 1600) ^ 0 *
        hpThetaJensenCellsBatch008Upper j * ((((160 : ℝ) + (j : ℝ) + 1) / 1600) - (((160 : ℝ) + (j
        : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch008_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 0
      (Or.inl rfl)).2
  have h2 : (∑ j ∈ Finset.range 20, (((160 : ℝ) + (j : ℝ)) / 1600) ^ 2 *
    hpThetaJensenCellsBatch008Lower j * ((((160 : ℝ) + (j : ℝ) + 1) / 1600) - (((160 : ℝ) + (j :
    ℝ)) / 1600))) ≤
      ∑ j ∈ Finset.range 20,
        ∫ u : ℝ in Set.Ioo (((160 : ℝ) + (j : ℝ)) / 1600) (((160 : ℝ) + (j : ℝ) + 1) / 1600), u ^
          2 * hpRiemannThetaDifferentialKernel u := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch008_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 2
      (Or.inr (Or.inl rfl))).1
  have h4 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((160 : ℝ) + (j : ℝ)) / 1600) (((160 : ℝ) + (j : ℝ) + 1) / 1600), u ^ 4
        * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((160 : ℝ) + (j : ℝ) + 1) / 1600) ^ 4 *
        hpThetaJensenCellsBatch008Upper j * ((((160 : ℝ) + (j : ℝ) + 1) / 1600) - (((160 : ℝ) + (j
        : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch008_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 4
      (Or.inr (Or.inr rfl))).2
  rw [hs 0 (Or.inl rfl)] at h0
  rw [hs 2 (Or.inr (Or.inl rfl))] at h2
  rw [hs 4 (Or.inr (Or.inr rfl))] at h4
  norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch008Lower,
    hpThetaJensenCellsBatch008Upper] at h0 h2 h4
  norm_num [hpThetaJensenBatchZeroUpper, hpThetaJensenBatchSecondLower,
    hpThetaJensenBatchFourthUpper]
  exact ⟨le_trans h0 (by norm_num), le_trans (by norm_num) h2,
    le_trans h4 (by norm_num)⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Twenty rational terms are verified for each of the three moment orders.
theorem hpThetaJensenCellsBatch009_finiteIntegral_bounds :
    (∫ u : ℝ in Set.Ioo (9 / 80 : ℝ) ((9 + 1) / 80 : ℝ), u ^ 0 * hpRiemannThetaDifferentialKernel
      u) ≤
        hpThetaJensenBatchZeroUpper 9 ∧
    hpThetaJensenBatchSecondLower 9 ≤
        (∫ u : ℝ in Set.Ioo (9 / 80 : ℝ) ((9 + 1) / 80 : ℝ), u ^ 2 *
          hpRiemannThetaDifferentialKernel u) ∧
    (∫ u : ℝ in Set.Ioo (9 / 80 : ℝ) ((9 + 1) / 80 : ℝ), u ^ 4 * hpRiemannThetaDifferentialKernel
      u) ≤
        hpThetaJensenBatchFourthUpper 9 := by
  have hs (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
      (∑ j ∈ Finset.range 20, ∫ u : ℝ in Set.Ioo (((180 : ℝ) + (j : ℝ)) / 1600) (((180 : ℝ) + (j :
        ℝ) + 1) / 1600),
        u ^ m * hpRiemannThetaDifferentialKernel u) =
      ∫ u : ℝ in Set.Ioo (9 / 80 : ℝ) ((9 + 1) / 80 : ℝ), u ^ m * hpRiemannThetaDifferentialKernel
        u := by
    have h := hpThetaJensen_batchCellIntegral_sum m hm 9
    have hc : ∀ j : ℕ,
        Set.Ioo (((180 : ℝ) + (j : ℝ)) / 1600) (((180 : ℝ) + (j : ℝ) + 1) / 1600) =
          Set.Ioo ((9 : ℝ) / 80 + (j : ℝ) / 1600)
            ((9 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600) := by
      intro j
      have hl : (((180 : ℝ) + (j : ℝ)) / 1600) = (9 : ℝ) / 80 + (j : ℝ) / 1600 := by ring
      have hr : (((180 : ℝ) + (j : ℝ) + 1) / 1600) = (9 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600 := by
        push_cast
        ring
      rw [hl, hr]
    simp_rw [hc]
    exact h
  have h0 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((180 : ℝ) + (j : ℝ)) / 1600) (((180 : ℝ) + (j : ℝ) + 1) / 1600), u ^ 0
        * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((180 : ℝ) + (j : ℝ) + 1) / 1600) ^ 0 *
        hpThetaJensenCellsBatch009Upper j * ((((180 : ℝ) + (j : ℝ) + 1) / 1600) - (((180 : ℝ) + (j
        : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch009_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 0
      (Or.inl rfl)).2
  have h2 : (∑ j ∈ Finset.range 20, (((180 : ℝ) + (j : ℝ)) / 1600) ^ 2 *
    hpThetaJensenCellsBatch009Lower j * ((((180 : ℝ) + (j : ℝ) + 1) / 1600) - (((180 : ℝ) + (j :
    ℝ)) / 1600))) ≤
      ∑ j ∈ Finset.range 20,
        ∫ u : ℝ in Set.Ioo (((180 : ℝ) + (j : ℝ)) / 1600) (((180 : ℝ) + (j : ℝ) + 1) / 1600), u ^
          2 * hpRiemannThetaDifferentialKernel u := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch009_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 2
      (Or.inr (Or.inl rfl))).1
  have h4 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((180 : ℝ) + (j : ℝ)) / 1600) (((180 : ℝ) + (j : ℝ) + 1) / 1600), u ^ 4
        * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((180 : ℝ) + (j : ℝ) + 1) / 1600) ^ 4 *
        hpThetaJensenCellsBatch009Upper j * ((((180 : ℝ) + (j : ℝ) + 1) / 1600) - (((180 : ℝ) + (j
        : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch009_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 4
      (Or.inr (Or.inr rfl))).2
  rw [hs 0 (Or.inl rfl)] at h0
  rw [hs 2 (Or.inr (Or.inl rfl))] at h2
  rw [hs 4 (Or.inr (Or.inr rfl))] at h4
  norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch009Lower,
    hpThetaJensenCellsBatch009Upper] at h0 h2 h4
  norm_num [hpThetaJensenBatchZeroUpper, hpThetaJensenBatchSecondLower,
    hpThetaJensenBatchFourthUpper]
  exact ⟨le_trans h0 (by norm_num), le_trans (by norm_num) h2,
    le_trans h4 (by norm_num)⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Twenty rational terms are verified for each of the three moment orders.
theorem hpThetaJensenCellsBatch010_finiteIntegral_bounds :
    (∫ u : ℝ in Set.Ioo (10 / 80 : ℝ) ((10 + 1) / 80 : ℝ), u ^ 0 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchZeroUpper 10 ∧
    hpThetaJensenBatchSecondLower 10 ≤
        (∫ u : ℝ in Set.Ioo (10 / 80 : ℝ) ((10 + 1) / 80 : ℝ), u ^ 2 *
          hpRiemannThetaDifferentialKernel u) ∧
    (∫ u : ℝ in Set.Ioo (10 / 80 : ℝ) ((10 + 1) / 80 : ℝ), u ^ 4 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchFourthUpper 10 := by
  have hs (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
      (∑ j ∈ Finset.range 20, ∫ u : ℝ in Set.Ioo (((200 : ℝ) + (j : ℝ)) / 1600) (((200 : ℝ) + (j :
        ℝ) + 1) / 1600),
        u ^ m * hpRiemannThetaDifferentialKernel u) =
      ∫ u : ℝ in Set.Ioo (10 / 80 : ℝ) ((10 + 1) / 80 : ℝ), u ^ m *
        hpRiemannThetaDifferentialKernel u := by
    have h := hpThetaJensen_batchCellIntegral_sum m hm 10
    have hc : ∀ j : ℕ,
        Set.Ioo (((200 : ℝ) + (j : ℝ)) / 1600) (((200 : ℝ) + (j : ℝ) + 1) / 1600) =
          Set.Ioo ((10 : ℝ) / 80 + (j : ℝ) / 1600)
            ((10 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600) := by
      intro j
      have hl : (((200 : ℝ) + (j : ℝ)) / 1600) = (10 : ℝ) / 80 + (j : ℝ) / 1600 := by ring
      have hr : (((200 : ℝ) + (j : ℝ) + 1) / 1600) = (10 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600 :=
        by
        push_cast
        ring
      rw [hl, hr]
    simp_rw [hc]
    exact h
  have h0 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((200 : ℝ) + (j : ℝ)) / 1600) (((200 : ℝ) + (j : ℝ) + 1) / 1600), u ^ 0
        * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((200 : ℝ) + (j : ℝ) + 1) / 1600) ^ 0 *
        hpThetaJensenCellsBatch010Upper j * ((((200 : ℝ) + (j : ℝ) + 1) / 1600) - (((200 : ℝ) + (j
        : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch010_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 0
      (Or.inl rfl)).2
  have h2 : (∑ j ∈ Finset.range 20, (((200 : ℝ) + (j : ℝ)) / 1600) ^ 2 *
    hpThetaJensenCellsBatch010Lower j * ((((200 : ℝ) + (j : ℝ) + 1) / 1600) - (((200 : ℝ) + (j :
    ℝ)) / 1600))) ≤
      ∑ j ∈ Finset.range 20,
        ∫ u : ℝ in Set.Ioo (((200 : ℝ) + (j : ℝ)) / 1600) (((200 : ℝ) + (j : ℝ) + 1) / 1600), u ^
          2 * hpRiemannThetaDifferentialKernel u := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch010_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 2
      (Or.inr (Or.inl rfl))).1
  have h4 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((200 : ℝ) + (j : ℝ)) / 1600) (((200 : ℝ) + (j : ℝ) + 1) / 1600), u ^ 4
        * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((200 : ℝ) + (j : ℝ) + 1) / 1600) ^ 4 *
        hpThetaJensenCellsBatch010Upper j * ((((200 : ℝ) + (j : ℝ) + 1) / 1600) - (((200 : ℝ) + (j
        : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch010_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 4
      (Or.inr (Or.inr rfl))).2
  rw [hs 0 (Or.inl rfl)] at h0
  rw [hs 2 (Or.inr (Or.inl rfl))] at h2
  rw [hs 4 (Or.inr (Or.inr rfl))] at h4
  norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch010Lower,
    hpThetaJensenCellsBatch010Upper] at h0 h2 h4
  norm_num [hpThetaJensenBatchZeroUpper, hpThetaJensenBatchSecondLower,
    hpThetaJensenBatchFourthUpper]
  exact ⟨le_trans h0 (by norm_num), le_trans (by norm_num) h2,
    le_trans h4 (by norm_num)⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Twenty rational terms are verified for each of the three moment orders.
theorem hpThetaJensenCellsBatch011_finiteIntegral_bounds :
    (∫ u : ℝ in Set.Ioo (11 / 80 : ℝ) ((11 + 1) / 80 : ℝ), u ^ 0 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchZeroUpper 11 ∧
    hpThetaJensenBatchSecondLower 11 ≤
        (∫ u : ℝ in Set.Ioo (11 / 80 : ℝ) ((11 + 1) / 80 : ℝ), u ^ 2 *
          hpRiemannThetaDifferentialKernel u) ∧
    (∫ u : ℝ in Set.Ioo (11 / 80 : ℝ) ((11 + 1) / 80 : ℝ), u ^ 4 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchFourthUpper 11 := by
  have hs (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
      (∑ j ∈ Finset.range 20, ∫ u : ℝ in Set.Ioo (((220 : ℝ) + (j : ℝ)) / 1600) (((220 : ℝ) + (j :
        ℝ) + 1) / 1600),
        u ^ m * hpRiemannThetaDifferentialKernel u) =
      ∫ u : ℝ in Set.Ioo (11 / 80 : ℝ) ((11 + 1) / 80 : ℝ), u ^ m *
        hpRiemannThetaDifferentialKernel u := by
    have h := hpThetaJensen_batchCellIntegral_sum m hm 11
    have hc : ∀ j : ℕ,
        Set.Ioo (((220 : ℝ) + (j : ℝ)) / 1600) (((220 : ℝ) + (j : ℝ) + 1) / 1600) =
          Set.Ioo ((11 : ℝ) / 80 + (j : ℝ) / 1600)
            ((11 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600) := by
      intro j
      have hl : (((220 : ℝ) + (j : ℝ)) / 1600) = (11 : ℝ) / 80 + (j : ℝ) / 1600 := by ring
      have hr : (((220 : ℝ) + (j : ℝ) + 1) / 1600) = (11 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600 :=
        by
        push_cast
        ring
      rw [hl, hr]
    simp_rw [hc]
    exact h
  have h0 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((220 : ℝ) + (j : ℝ)) / 1600) (((220 : ℝ) + (j : ℝ) + 1) / 1600), u ^ 0
        * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((220 : ℝ) + (j : ℝ) + 1) / 1600) ^ 0 *
        hpThetaJensenCellsBatch011Upper j * ((((220 : ℝ) + (j : ℝ) + 1) / 1600) - (((220 : ℝ) + (j
        : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch011_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 0
      (Or.inl rfl)).2
  have h2 : (∑ j ∈ Finset.range 20, (((220 : ℝ) + (j : ℝ)) / 1600) ^ 2 *
    hpThetaJensenCellsBatch011Lower j * ((((220 : ℝ) + (j : ℝ) + 1) / 1600) - (((220 : ℝ) + (j :
    ℝ)) / 1600))) ≤
      ∑ j ∈ Finset.range 20,
        ∫ u : ℝ in Set.Ioo (((220 : ℝ) + (j : ℝ)) / 1600) (((220 : ℝ) + (j : ℝ) + 1) / 1600), u ^
          2 * hpRiemannThetaDifferentialKernel u := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch011_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 2
      (Or.inr (Or.inl rfl))).1
  have h4 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((220 : ℝ) + (j : ℝ)) / 1600) (((220 : ℝ) + (j : ℝ) + 1) / 1600), u ^ 4
        * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((220 : ℝ) + (j : ℝ) + 1) / 1600) ^ 4 *
        hpThetaJensenCellsBatch011Upper j * ((((220 : ℝ) + (j : ℝ) + 1) / 1600) - (((220 : ℝ) + (j
        : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch011_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 4
      (Or.inr (Or.inr rfl))).2
  rw [hs 0 (Or.inl rfl)] at h0
  rw [hs 2 (Or.inr (Or.inl rfl))] at h2
  rw [hs 4 (Or.inr (Or.inr rfl))] at h4
  norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch011Lower,
    hpThetaJensenCellsBatch011Upper] at h0 h2 h4
  norm_num [hpThetaJensenBatchZeroUpper, hpThetaJensenBatchSecondLower,
    hpThetaJensenBatchFourthUpper]
  exact ⟨le_trans h0 (by norm_num), le_trans (by norm_num) h2,
    le_trans h4 (by norm_num)⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Twenty rational terms are verified for each of the three moment orders.
theorem hpThetaJensenCellsBatch012_finiteIntegral_bounds :
    (∫ u : ℝ in Set.Ioo (12 / 80 : ℝ) ((12 + 1) / 80 : ℝ), u ^ 0 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchZeroUpper 12 ∧
    hpThetaJensenBatchSecondLower 12 ≤
        (∫ u : ℝ in Set.Ioo (12 / 80 : ℝ) ((12 + 1) / 80 : ℝ), u ^ 2 *
          hpRiemannThetaDifferentialKernel u) ∧
    (∫ u : ℝ in Set.Ioo (12 / 80 : ℝ) ((12 + 1) / 80 : ℝ), u ^ 4 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchFourthUpper 12 := by
  have hs (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
      (∑ j ∈ Finset.range 20, ∫ u : ℝ in Set.Ioo (((240 : ℝ) + (j : ℝ)) / 1600) (((240 : ℝ) + (j :
        ℝ) + 1) / 1600),
        u ^ m * hpRiemannThetaDifferentialKernel u) =
      ∫ u : ℝ in Set.Ioo (12 / 80 : ℝ) ((12 + 1) / 80 : ℝ), u ^ m *
        hpRiemannThetaDifferentialKernel u := by
    have h := hpThetaJensen_batchCellIntegral_sum m hm 12
    have hc : ∀ j : ℕ,
        Set.Ioo (((240 : ℝ) + (j : ℝ)) / 1600) (((240 : ℝ) + (j : ℝ) + 1) / 1600) =
          Set.Ioo ((12 : ℝ) / 80 + (j : ℝ) / 1600)
            ((12 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600) := by
      intro j
      have hl : (((240 : ℝ) + (j : ℝ)) / 1600) = (12 : ℝ) / 80 + (j : ℝ) / 1600 := by ring
      have hr : (((240 : ℝ) + (j : ℝ) + 1) / 1600) = (12 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600 :=
        by
        push_cast
        ring
      rw [hl, hr]
    simp_rw [hc]
    exact h
  have h0 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((240 : ℝ) + (j : ℝ)) / 1600) (((240 : ℝ) + (j : ℝ) + 1) / 1600), u ^ 0
        * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((240 : ℝ) + (j : ℝ) + 1) / 1600) ^ 0 *
        hpThetaJensenCellsBatch012Upper j * ((((240 : ℝ) + (j : ℝ) + 1) / 1600) - (((240 : ℝ) + (j
        : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch012_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 0
      (Or.inl rfl)).2
  have h2 : (∑ j ∈ Finset.range 20, (((240 : ℝ) + (j : ℝ)) / 1600) ^ 2 *
    hpThetaJensenCellsBatch012Lower j * ((((240 : ℝ) + (j : ℝ) + 1) / 1600) - (((240 : ℝ) + (j :
    ℝ)) / 1600))) ≤
      ∑ j ∈ Finset.range 20,
        ∫ u : ℝ in Set.Ioo (((240 : ℝ) + (j : ℝ)) / 1600) (((240 : ℝ) + (j : ℝ) + 1) / 1600), u ^
          2 * hpRiemannThetaDifferentialKernel u := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch012_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 2
      (Or.inr (Or.inl rfl))).1
  have h4 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((240 : ℝ) + (j : ℝ)) / 1600) (((240 : ℝ) + (j : ℝ) + 1) / 1600), u ^ 4
        * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((240 : ℝ) + (j : ℝ) + 1) / 1600) ^ 4 *
        hpThetaJensenCellsBatch012Upper j * ((((240 : ℝ) + (j : ℝ) + 1) / 1600) - (((240 : ℝ) + (j
        : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch012_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 4
      (Or.inr (Or.inr rfl))).2
  rw [hs 0 (Or.inl rfl)] at h0
  rw [hs 2 (Or.inr (Or.inl rfl))] at h2
  rw [hs 4 (Or.inr (Or.inr rfl))] at h4
  norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch012Lower,
    hpThetaJensenCellsBatch012Upper] at h0 h2 h4
  norm_num [hpThetaJensenBatchZeroUpper, hpThetaJensenBatchSecondLower,
    hpThetaJensenBatchFourthUpper]
  exact ⟨le_trans h0 (by norm_num), le_trans (by norm_num) h2,
    le_trans h4 (by norm_num)⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Twenty rational terms are verified for each of the three moment orders.
theorem hpThetaJensenCellsBatch013_finiteIntegral_bounds :
    (∫ u : ℝ in Set.Ioo (13 / 80 : ℝ) ((13 + 1) / 80 : ℝ), u ^ 0 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchZeroUpper 13 ∧
    hpThetaJensenBatchSecondLower 13 ≤
        (∫ u : ℝ in Set.Ioo (13 / 80 : ℝ) ((13 + 1) / 80 : ℝ), u ^ 2 *
          hpRiemannThetaDifferentialKernel u) ∧
    (∫ u : ℝ in Set.Ioo (13 / 80 : ℝ) ((13 + 1) / 80 : ℝ), u ^ 4 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchFourthUpper 13 := by
  have hs (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
      (∑ j ∈ Finset.range 20, ∫ u : ℝ in Set.Ioo (((260 : ℝ) + (j : ℝ)) / 1600) (((260 : ℝ) + (j :
        ℝ) + 1) / 1600),
        u ^ m * hpRiemannThetaDifferentialKernel u) =
      ∫ u : ℝ in Set.Ioo (13 / 80 : ℝ) ((13 + 1) / 80 : ℝ), u ^ m *
        hpRiemannThetaDifferentialKernel u := by
    have h := hpThetaJensen_batchCellIntegral_sum m hm 13
    have hc : ∀ j : ℕ,
        Set.Ioo (((260 : ℝ) + (j : ℝ)) / 1600) (((260 : ℝ) + (j : ℝ) + 1) / 1600) =
          Set.Ioo ((13 : ℝ) / 80 + (j : ℝ) / 1600)
            ((13 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600) := by
      intro j
      have hl : (((260 : ℝ) + (j : ℝ)) / 1600) = (13 : ℝ) / 80 + (j : ℝ) / 1600 := by ring
      have hr : (((260 : ℝ) + (j : ℝ) + 1) / 1600) = (13 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600 :=
        by
        push_cast
        ring
      rw [hl, hr]
    simp_rw [hc]
    exact h
  have h0 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((260 : ℝ) + (j : ℝ)) / 1600) (((260 : ℝ) + (j : ℝ) + 1) / 1600), u ^ 0
        * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((260 : ℝ) + (j : ℝ) + 1) / 1600) ^ 0 *
        hpThetaJensenCellsBatch013Upper j * ((((260 : ℝ) + (j : ℝ) + 1) / 1600) - (((260 : ℝ) + (j
        : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch013_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 0
      (Or.inl rfl)).2
  have h2 : (∑ j ∈ Finset.range 20, (((260 : ℝ) + (j : ℝ)) / 1600) ^ 2 *
    hpThetaJensenCellsBatch013Lower j * ((((260 : ℝ) + (j : ℝ) + 1) / 1600) - (((260 : ℝ) + (j :
    ℝ)) / 1600))) ≤
      ∑ j ∈ Finset.range 20,
        ∫ u : ℝ in Set.Ioo (((260 : ℝ) + (j : ℝ)) / 1600) (((260 : ℝ) + (j : ℝ) + 1) / 1600), u ^
          2 * hpRiemannThetaDifferentialKernel u := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch013_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 2
      (Or.inr (Or.inl rfl))).1
  have h4 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((260 : ℝ) + (j : ℝ)) / 1600) (((260 : ℝ) + (j : ℝ) + 1) / 1600), u ^ 4
        * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((260 : ℝ) + (j : ℝ) + 1) / 1600) ^ 4 *
        hpThetaJensenCellsBatch013Upper j * ((((260 : ℝ) + (j : ℝ) + 1) / 1600) - (((260 : ℝ) + (j
        : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch013_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 4
      (Or.inr (Or.inr rfl))).2
  rw [hs 0 (Or.inl rfl)] at h0
  rw [hs 2 (Or.inr (Or.inl rfl))] at h2
  rw [hs 4 (Or.inr (Or.inr rfl))] at h4
  norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch013Lower,
    hpThetaJensenCellsBatch013Upper] at h0 h2 h4
  norm_num [hpThetaJensenBatchZeroUpper, hpThetaJensenBatchSecondLower,
    hpThetaJensenBatchFourthUpper]
  exact ⟨le_trans h0 (by norm_num), le_trans (by norm_num) h2,
    le_trans h4 (by norm_num)⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Twenty rational terms are verified for each of the three moment orders.
theorem hpThetaJensenCellsBatch014_finiteIntegral_bounds :
    (∫ u : ℝ in Set.Ioo (14 / 80 : ℝ) ((14 + 1) / 80 : ℝ), u ^ 0 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchZeroUpper 14 ∧
    hpThetaJensenBatchSecondLower 14 ≤
        (∫ u : ℝ in Set.Ioo (14 / 80 : ℝ) ((14 + 1) / 80 : ℝ), u ^ 2 *
          hpRiemannThetaDifferentialKernel u) ∧
    (∫ u : ℝ in Set.Ioo (14 / 80 : ℝ) ((14 + 1) / 80 : ℝ), u ^ 4 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchFourthUpper 14 := by
  have hs (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
      (∑ j ∈ Finset.range 20, ∫ u : ℝ in Set.Ioo (((280 : ℝ) + (j : ℝ)) / 1600) (((280 : ℝ) + (j :
        ℝ) + 1) / 1600),
        u ^ m * hpRiemannThetaDifferentialKernel u) =
      ∫ u : ℝ in Set.Ioo (14 / 80 : ℝ) ((14 + 1) / 80 : ℝ), u ^ m *
        hpRiemannThetaDifferentialKernel u := by
    have h := hpThetaJensen_batchCellIntegral_sum m hm 14
    have hc : ∀ j : ℕ,
        Set.Ioo (((280 : ℝ) + (j : ℝ)) / 1600) (((280 : ℝ) + (j : ℝ) + 1) / 1600) =
          Set.Ioo ((14 : ℝ) / 80 + (j : ℝ) / 1600)
            ((14 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600) := by
      intro j
      have hl : (((280 : ℝ) + (j : ℝ)) / 1600) = (14 : ℝ) / 80 + (j : ℝ) / 1600 := by ring
      have hr : (((280 : ℝ) + (j : ℝ) + 1) / 1600) = (14 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600 :=
        by
        push_cast
        ring
      rw [hl, hr]
    simp_rw [hc]
    exact h
  have h0 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((280 : ℝ) + (j : ℝ)) / 1600) (((280 : ℝ) + (j : ℝ) + 1) / 1600), u ^ 0
        * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((280 : ℝ) + (j : ℝ) + 1) / 1600) ^ 0 *
        hpThetaJensenCellsBatch014Upper j * ((((280 : ℝ) + (j : ℝ) + 1) / 1600) - (((280 : ℝ) + (j
        : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch014_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 0
      (Or.inl rfl)).2
  have h2 : (∑ j ∈ Finset.range 20, (((280 : ℝ) + (j : ℝ)) / 1600) ^ 2 *
    hpThetaJensenCellsBatch014Lower j * ((((280 : ℝ) + (j : ℝ) + 1) / 1600) - (((280 : ℝ) + (j :
    ℝ)) / 1600))) ≤
      ∑ j ∈ Finset.range 20,
        ∫ u : ℝ in Set.Ioo (((280 : ℝ) + (j : ℝ)) / 1600) (((280 : ℝ) + (j : ℝ) + 1) / 1600), u ^
          2 * hpRiemannThetaDifferentialKernel u := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch014_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 2
      (Or.inr (Or.inl rfl))).1
  have h4 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((280 : ℝ) + (j : ℝ)) / 1600) (((280 : ℝ) + (j : ℝ) + 1) / 1600), u ^ 4
        * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((280 : ℝ) + (j : ℝ) + 1) / 1600) ^ 4 *
        hpThetaJensenCellsBatch014Upper j * ((((280 : ℝ) + (j : ℝ) + 1) / 1600) - (((280 : ℝ) + (j
        : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch014_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 4
      (Or.inr (Or.inr rfl))).2
  rw [hs 0 (Or.inl rfl)] at h0
  rw [hs 2 (Or.inr (Or.inl rfl))] at h2
  rw [hs 4 (Or.inr (Or.inr rfl))] at h4
  norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch014Lower,
    hpThetaJensenCellsBatch014Upper] at h0 h2 h4
  norm_num [hpThetaJensenBatchZeroUpper, hpThetaJensenBatchSecondLower,
    hpThetaJensenBatchFourthUpper]
  exact ⟨le_trans h0 (by norm_num), le_trans (by norm_num) h2,
    le_trans h4 (by norm_num)⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Twenty rational terms are verified for each of the three moment orders.
theorem hpThetaJensenCellsBatch015_finiteIntegral_bounds :
    (∫ u : ℝ in Set.Ioo (15 / 80 : ℝ) ((15 + 1) / 80 : ℝ), u ^ 0 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchZeroUpper 15 ∧
    hpThetaJensenBatchSecondLower 15 ≤
        (∫ u : ℝ in Set.Ioo (15 / 80 : ℝ) ((15 + 1) / 80 : ℝ), u ^ 2 *
          hpRiemannThetaDifferentialKernel u) ∧
    (∫ u : ℝ in Set.Ioo (15 / 80 : ℝ) ((15 + 1) / 80 : ℝ), u ^ 4 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchFourthUpper 15 := by
  have hs (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
      (∑ j ∈ Finset.range 20, ∫ u : ℝ in Set.Ioo (((300 : ℝ) + (j : ℝ)) / 1600) (((300 : ℝ) + (j :
        ℝ) + 1) / 1600),
        u ^ m * hpRiemannThetaDifferentialKernel u) =
      ∫ u : ℝ in Set.Ioo (15 / 80 : ℝ) ((15 + 1) / 80 : ℝ), u ^ m *
        hpRiemannThetaDifferentialKernel u := by
    have h := hpThetaJensen_batchCellIntegral_sum m hm 15
    have hc : ∀ j : ℕ,
        Set.Ioo (((300 : ℝ) + (j : ℝ)) / 1600) (((300 : ℝ) + (j : ℝ) + 1) / 1600) =
          Set.Ioo ((15 : ℝ) / 80 + (j : ℝ) / 1600)
            ((15 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600) := by
      intro j
      have hl : (((300 : ℝ) + (j : ℝ)) / 1600) = (15 : ℝ) / 80 + (j : ℝ) / 1600 := by ring
      have hr : (((300 : ℝ) + (j : ℝ) + 1) / 1600) = (15 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600 :=
        by
        push_cast
        ring
      rw [hl, hr]
    simp_rw [hc]
    exact h
  have h0 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((300 : ℝ) + (j : ℝ)) / 1600) (((300 : ℝ) + (j : ℝ) + 1) / 1600), u ^ 0
        * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((300 : ℝ) + (j : ℝ) + 1) / 1600) ^ 0 *
        hpThetaJensenCellsBatch015Upper j * ((((300 : ℝ) + (j : ℝ) + 1) / 1600) - (((300 : ℝ) + (j
        : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch015_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 0
      (Or.inl rfl)).2
  have h2 : (∑ j ∈ Finset.range 20, (((300 : ℝ) + (j : ℝ)) / 1600) ^ 2 *
    hpThetaJensenCellsBatch015Lower j * ((((300 : ℝ) + (j : ℝ) + 1) / 1600) - (((300 : ℝ) + (j :
    ℝ)) / 1600))) ≤
      ∑ j ∈ Finset.range 20,
        ∫ u : ℝ in Set.Ioo (((300 : ℝ) + (j : ℝ)) / 1600) (((300 : ℝ) + (j : ℝ) + 1) / 1600), u ^
          2 * hpRiemannThetaDifferentialKernel u := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch015_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 2
      (Or.inr (Or.inl rfl))).1
  have h4 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((300 : ℝ) + (j : ℝ)) / 1600) (((300 : ℝ) + (j : ℝ) + 1) / 1600), u ^ 4
        * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((300 : ℝ) + (j : ℝ) + 1) / 1600) ^ 4 *
        hpThetaJensenCellsBatch015Upper j * ((((300 : ℝ) + (j : ℝ) + 1) / 1600) - (((300 : ℝ) + (j
        : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch015_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 4
      (Or.inr (Or.inr rfl))).2
  rw [hs 0 (Or.inl rfl)] at h0
  rw [hs 2 (Or.inr (Or.inl rfl))] at h2
  rw [hs 4 (Or.inr (Or.inr rfl))] at h4
  norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch015Lower,
    hpThetaJensenCellsBatch015Upper] at h0 h2 h4
  norm_num [hpThetaJensenBatchZeroUpper, hpThetaJensenBatchSecondLower,
    hpThetaJensenBatchFourthUpper]
  exact ⟨le_trans h0 (by norm_num), le_trans (by norm_num) h2,
    le_trans h4 (by norm_num)⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Twenty rational terms are verified for each of the three moment orders.
theorem hpThetaJensenCellsBatch016_finiteIntegral_bounds :
    (∫ u : ℝ in Set.Ioo (16 / 80 : ℝ) ((16 + 1) / 80 : ℝ), u ^ 0 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchZeroUpper 16 ∧
    hpThetaJensenBatchSecondLower 16 ≤
        (∫ u : ℝ in Set.Ioo (16 / 80 : ℝ) ((16 + 1) / 80 : ℝ), u ^ 2 *
          hpRiemannThetaDifferentialKernel u) ∧
    (∫ u : ℝ in Set.Ioo (16 / 80 : ℝ) ((16 + 1) / 80 : ℝ), u ^ 4 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchFourthUpper 16 := by
  have hs (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
      (∑ j ∈ Finset.range 20, ∫ u : ℝ in Set.Ioo (((320 : ℝ) + (j : ℝ)) / 1600) (((320 : ℝ) + (j :
        ℝ) + 1) / 1600),
        u ^ m * hpRiemannThetaDifferentialKernel u) =
      ∫ u : ℝ in Set.Ioo (16 / 80 : ℝ) ((16 + 1) / 80 : ℝ), u ^ m *
        hpRiemannThetaDifferentialKernel u := by
    have h := hpThetaJensen_batchCellIntegral_sum m hm 16
    have hc : ∀ j : ℕ,
        Set.Ioo (((320 : ℝ) + (j : ℝ)) / 1600) (((320 : ℝ) + (j : ℝ) + 1) / 1600) =
          Set.Ioo ((16 : ℝ) / 80 + (j : ℝ) / 1600)
            ((16 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600) := by
      intro j
      have hl : (((320 : ℝ) + (j : ℝ)) / 1600) = (16 : ℝ) / 80 + (j : ℝ) / 1600 := by ring
      have hr : (((320 : ℝ) + (j : ℝ) + 1) / 1600) = (16 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600 :=
        by
        push_cast
        ring
      rw [hl, hr]
    simp_rw [hc]
    exact h
  have h0 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((320 : ℝ) + (j : ℝ)) / 1600) (((320 : ℝ) + (j : ℝ) + 1) / 1600), u ^ 0
        * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((320 : ℝ) + (j : ℝ) + 1) / 1600) ^ 0 *
        hpThetaJensenCellsBatch016Upper j * ((((320 : ℝ) + (j : ℝ) + 1) / 1600) - (((320 : ℝ) + (j
        : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch016_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 0
      (Or.inl rfl)).2
  have h2 : (∑ j ∈ Finset.range 20, (((320 : ℝ) + (j : ℝ)) / 1600) ^ 2 *
    hpThetaJensenCellsBatch016Lower j * ((((320 : ℝ) + (j : ℝ) + 1) / 1600) - (((320 : ℝ) + (j :
    ℝ)) / 1600))) ≤
      ∑ j ∈ Finset.range 20,
        ∫ u : ℝ in Set.Ioo (((320 : ℝ) + (j : ℝ)) / 1600) (((320 : ℝ) + (j : ℝ) + 1) / 1600), u ^
          2 * hpRiemannThetaDifferentialKernel u := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch016_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 2
      (Or.inr (Or.inl rfl))).1
  have h4 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((320 : ℝ) + (j : ℝ)) / 1600) (((320 : ℝ) + (j : ℝ) + 1) / 1600), u ^ 4
        * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((320 : ℝ) + (j : ℝ) + 1) / 1600) ^ 4 *
        hpThetaJensenCellsBatch016Upper j * ((((320 : ℝ) + (j : ℝ) + 1) / 1600) - (((320 : ℝ) + (j
        : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch016_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 4
      (Or.inr (Or.inr rfl))).2
  rw [hs 0 (Or.inl rfl)] at h0
  rw [hs 2 (Or.inr (Or.inl rfl))] at h2
  rw [hs 4 (Or.inr (Or.inr rfl))] at h4
  norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch016Lower,
    hpThetaJensenCellsBatch016Upper] at h0 h2 h4
  norm_num [hpThetaJensenBatchZeroUpper, hpThetaJensenBatchSecondLower,
    hpThetaJensenBatchFourthUpper]
  exact ⟨le_trans h0 (by norm_num), le_trans (by norm_num) h2,
    le_trans h4 (by norm_num)⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Twenty rational terms are verified for each of the three moment orders.
theorem hpThetaJensenCellsBatch017_finiteIntegral_bounds :
    (∫ u : ℝ in Set.Ioo (17 / 80 : ℝ) ((17 + 1) / 80 : ℝ), u ^ 0 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchZeroUpper 17 ∧
    hpThetaJensenBatchSecondLower 17 ≤
        (∫ u : ℝ in Set.Ioo (17 / 80 : ℝ) ((17 + 1) / 80 : ℝ), u ^ 2 *
          hpRiemannThetaDifferentialKernel u) ∧
    (∫ u : ℝ in Set.Ioo (17 / 80 : ℝ) ((17 + 1) / 80 : ℝ), u ^ 4 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchFourthUpper 17 := by
  have hs (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
      (∑ j ∈ Finset.range 20, ∫ u : ℝ in Set.Ioo (((340 : ℝ) + (j : ℝ)) / 1600) (((340 : ℝ) + (j :
        ℝ) + 1) / 1600),
        u ^ m * hpRiemannThetaDifferentialKernel u) =
      ∫ u : ℝ in Set.Ioo (17 / 80 : ℝ) ((17 + 1) / 80 : ℝ), u ^ m *
        hpRiemannThetaDifferentialKernel u := by
    have h := hpThetaJensen_batchCellIntegral_sum m hm 17
    have hc : ∀ j : ℕ,
        Set.Ioo (((340 : ℝ) + (j : ℝ)) / 1600) (((340 : ℝ) + (j : ℝ) + 1) / 1600) =
          Set.Ioo ((17 : ℝ) / 80 + (j : ℝ) / 1600)
            ((17 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600) := by
      intro j
      have hl : (((340 : ℝ) + (j : ℝ)) / 1600) = (17 : ℝ) / 80 + (j : ℝ) / 1600 := by ring
      have hr : (((340 : ℝ) + (j : ℝ) + 1) / 1600) = (17 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600 :=
        by
        push_cast
        ring
      rw [hl, hr]
    simp_rw [hc]
    exact h
  have h0 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((340 : ℝ) + (j : ℝ)) / 1600) (((340 : ℝ) + (j : ℝ) + 1) / 1600), u ^ 0
        * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((340 : ℝ) + (j : ℝ) + 1) / 1600) ^ 0 *
        hpThetaJensenCellsBatch017Upper j * ((((340 : ℝ) + (j : ℝ) + 1) / 1600) - (((340 : ℝ) + (j
        : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch017_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 0
      (Or.inl rfl)).2
  have h2 : (∑ j ∈ Finset.range 20, (((340 : ℝ) + (j : ℝ)) / 1600) ^ 2 *
    hpThetaJensenCellsBatch017Lower j * ((((340 : ℝ) + (j : ℝ) + 1) / 1600) - (((340 : ℝ) + (j :
    ℝ)) / 1600))) ≤
      ∑ j ∈ Finset.range 20,
        ∫ u : ℝ in Set.Ioo (((340 : ℝ) + (j : ℝ)) / 1600) (((340 : ℝ) + (j : ℝ) + 1) / 1600), u ^
          2 * hpRiemannThetaDifferentialKernel u := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch017_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 2
      (Or.inr (Or.inl rfl))).1
  have h4 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((340 : ℝ) + (j : ℝ)) / 1600) (((340 : ℝ) + (j : ℝ) + 1) / 1600), u ^ 4
        * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((340 : ℝ) + (j : ℝ) + 1) / 1600) ^ 4 *
        hpThetaJensenCellsBatch017Upper j * ((((340 : ℝ) + (j : ℝ) + 1) / 1600) - (((340 : ℝ) + (j
        : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch017_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 4
      (Or.inr (Or.inr rfl))).2
  rw [hs 0 (Or.inl rfl)] at h0
  rw [hs 2 (Or.inr (Or.inl rfl))] at h2
  rw [hs 4 (Or.inr (Or.inr rfl))] at h4
  norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch017Lower,
    hpThetaJensenCellsBatch017Upper] at h0 h2 h4
  norm_num [hpThetaJensenBatchZeroUpper, hpThetaJensenBatchSecondLower,
    hpThetaJensenBatchFourthUpper]
  exact ⟨le_trans h0 (by norm_num), le_trans (by norm_num) h2,
    le_trans h4 (by norm_num)⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Twenty rational terms are verified for each of the three moment orders.
theorem hpThetaJensenCellsBatch018_finiteIntegral_bounds :
    (∫ u : ℝ in Set.Ioo (18 / 80 : ℝ) ((18 + 1) / 80 : ℝ), u ^ 0 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchZeroUpper 18 ∧
    hpThetaJensenBatchSecondLower 18 ≤
        (∫ u : ℝ in Set.Ioo (18 / 80 : ℝ) ((18 + 1) / 80 : ℝ), u ^ 2 *
          hpRiemannThetaDifferentialKernel u) ∧
    (∫ u : ℝ in Set.Ioo (18 / 80 : ℝ) ((18 + 1) / 80 : ℝ), u ^ 4 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchFourthUpper 18 := by
  have hs (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
      (∑ j ∈ Finset.range 20, ∫ u : ℝ in Set.Ioo (((360 : ℝ) + (j : ℝ)) / 1600) (((360 : ℝ) + (j :
        ℝ) + 1) / 1600),
        u ^ m * hpRiemannThetaDifferentialKernel u) =
      ∫ u : ℝ in Set.Ioo (18 / 80 : ℝ) ((18 + 1) / 80 : ℝ), u ^ m *
        hpRiemannThetaDifferentialKernel u := by
    have h := hpThetaJensen_batchCellIntegral_sum m hm 18
    have hc : ∀ j : ℕ,
        Set.Ioo (((360 : ℝ) + (j : ℝ)) / 1600) (((360 : ℝ) + (j : ℝ) + 1) / 1600) =
          Set.Ioo ((18 : ℝ) / 80 + (j : ℝ) / 1600)
            ((18 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600) := by
      intro j
      have hl : (((360 : ℝ) + (j : ℝ)) / 1600) = (18 : ℝ) / 80 + (j : ℝ) / 1600 := by ring
      have hr : (((360 : ℝ) + (j : ℝ) + 1) / 1600) = (18 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600 :=
        by
        push_cast
        ring
      rw [hl, hr]
    simp_rw [hc]
    exact h
  have h0 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((360 : ℝ) + (j : ℝ)) / 1600) (((360 : ℝ) + (j : ℝ) + 1) / 1600), u ^ 0
        * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((360 : ℝ) + (j : ℝ) + 1) / 1600) ^ 0 *
        hpThetaJensenCellsBatch018Upper j * ((((360 : ℝ) + (j : ℝ) + 1) / 1600) - (((360 : ℝ) + (j
        : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch018_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 0
      (Or.inl rfl)).2
  have h2 : (∑ j ∈ Finset.range 20, (((360 : ℝ) + (j : ℝ)) / 1600) ^ 2 *
    hpThetaJensenCellsBatch018Lower j * ((((360 : ℝ) + (j : ℝ) + 1) / 1600) - (((360 : ℝ) + (j :
    ℝ)) / 1600))) ≤
      ∑ j ∈ Finset.range 20,
        ∫ u : ℝ in Set.Ioo (((360 : ℝ) + (j : ℝ)) / 1600) (((360 : ℝ) + (j : ℝ) + 1) / 1600), u ^
          2 * hpRiemannThetaDifferentialKernel u := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch018_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 2
      (Or.inr (Or.inl rfl))).1
  have h4 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((360 : ℝ) + (j : ℝ)) / 1600) (((360 : ℝ) + (j : ℝ) + 1) / 1600), u ^ 4
        * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((360 : ℝ) + (j : ℝ) + 1) / 1600) ^ 4 *
        hpThetaJensenCellsBatch018Upper j * ((((360 : ℝ) + (j : ℝ) + 1) / 1600) - (((360 : ℝ) + (j
        : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch018_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 4
      (Or.inr (Or.inr rfl))).2
  rw [hs 0 (Or.inl rfl)] at h0
  rw [hs 2 (Or.inr (Or.inl rfl))] at h2
  rw [hs 4 (Or.inr (Or.inr rfl))] at h4
  norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch018Lower,
    hpThetaJensenCellsBatch018Upper] at h0 h2 h4
  norm_num [hpThetaJensenBatchZeroUpper, hpThetaJensenBatchSecondLower,
    hpThetaJensenBatchFourthUpper]
  exact ⟨le_trans h0 (by norm_num), le_trans (by norm_num) h2,
    le_trans h4 (by norm_num)⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Twenty rational terms are verified for each of the three moment orders.
theorem hpThetaJensenCellsBatch019_finiteIntegral_bounds :
    (∫ u : ℝ in Set.Ioo (19 / 80 : ℝ) ((19 + 1) / 80 : ℝ), u ^ 0 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchZeroUpper 19 ∧
    hpThetaJensenBatchSecondLower 19 ≤
        (∫ u : ℝ in Set.Ioo (19 / 80 : ℝ) ((19 + 1) / 80 : ℝ), u ^ 2 *
          hpRiemannThetaDifferentialKernel u) ∧
    (∫ u : ℝ in Set.Ioo (19 / 80 : ℝ) ((19 + 1) / 80 : ℝ), u ^ 4 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchFourthUpper 19 := by
  have hs (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
      (∑ j ∈ Finset.range 20, ∫ u : ℝ in Set.Ioo (((380 : ℝ) + (j : ℝ)) / 1600) (((380 : ℝ) + (j :
        ℝ) + 1) / 1600),
        u ^ m * hpRiemannThetaDifferentialKernel u) =
      ∫ u : ℝ in Set.Ioo (19 / 80 : ℝ) ((19 + 1) / 80 : ℝ), u ^ m *
        hpRiemannThetaDifferentialKernel u := by
    have h := hpThetaJensen_batchCellIntegral_sum m hm 19
    have hc : ∀ j : ℕ,
        Set.Ioo (((380 : ℝ) + (j : ℝ)) / 1600) (((380 : ℝ) + (j : ℝ) + 1) / 1600) =
          Set.Ioo ((19 : ℝ) / 80 + (j : ℝ) / 1600)
            ((19 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600) := by
      intro j
      have hl : (((380 : ℝ) + (j : ℝ)) / 1600) = (19 : ℝ) / 80 + (j : ℝ) / 1600 := by ring
      have hr : (((380 : ℝ) + (j : ℝ) + 1) / 1600) = (19 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600 :=
        by
        push_cast
        ring
      rw [hl, hr]
    simp_rw [hc]
    exact h
  have h0 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((380 : ℝ) + (j : ℝ)) / 1600) (((380 : ℝ) + (j : ℝ) + 1) / 1600), u ^ 0
        * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((380 : ℝ) + (j : ℝ) + 1) / 1600) ^ 0 *
        hpThetaJensenCellsBatch019Upper j * ((((380 : ℝ) + (j : ℝ) + 1) / 1600) - (((380 : ℝ) + (j
        : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch019_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 0
      (Or.inl rfl)).2
  have h2 : (∑ j ∈ Finset.range 20, (((380 : ℝ) + (j : ℝ)) / 1600) ^ 2 *
    hpThetaJensenCellsBatch019Lower j * ((((380 : ℝ) + (j : ℝ) + 1) / 1600) - (((380 : ℝ) + (j :
    ℝ)) / 1600))) ≤
      ∑ j ∈ Finset.range 20,
        ∫ u : ℝ in Set.Ioo (((380 : ℝ) + (j : ℝ)) / 1600) (((380 : ℝ) + (j : ℝ) + 1) / 1600), u ^
          2 * hpRiemannThetaDifferentialKernel u := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch019_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 2
      (Or.inr (Or.inl rfl))).1
  have h4 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((380 : ℝ) + (j : ℝ)) / 1600) (((380 : ℝ) + (j : ℝ) + 1) / 1600), u ^ 4
        * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((380 : ℝ) + (j : ℝ) + 1) / 1600) ^ 4 *
        hpThetaJensenCellsBatch019Upper j * ((((380 : ℝ) + (j : ℝ) + 1) / 1600) - (((380 : ℝ) + (j
        : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch019_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 4
      (Or.inr (Or.inr rfl))).2
  rw [hs 0 (Or.inl rfl)] at h0
  rw [hs 2 (Or.inr (Or.inl rfl))] at h2
  rw [hs 4 (Or.inr (Or.inr rfl))] at h4
  norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch019Lower,
    hpThetaJensenCellsBatch019Upper] at h0 h2 h4
  norm_num [hpThetaJensenBatchZeroUpper, hpThetaJensenBatchSecondLower,
    hpThetaJensenBatchFourthUpper]
  exact ⟨le_trans h0 (by norm_num), le_trans (by norm_num) h2,
    le_trans h4 (by norm_num)⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Twenty rational terms are verified for each of the three moment orders.
theorem hpThetaJensenCellsBatch020_finiteIntegral_bounds :
    (∫ u : ℝ in Set.Ioo (20 / 80 : ℝ) ((20 + 1) / 80 : ℝ), u ^ 0 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchZeroUpper 20 ∧
    hpThetaJensenBatchSecondLower 20 ≤
        (∫ u : ℝ in Set.Ioo (20 / 80 : ℝ) ((20 + 1) / 80 : ℝ), u ^ 2 *
          hpRiemannThetaDifferentialKernel u) ∧
    (∫ u : ℝ in Set.Ioo (20 / 80 : ℝ) ((20 + 1) / 80 : ℝ), u ^ 4 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchFourthUpper 20 := by
  have hs (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
      (∑ j ∈ Finset.range 20, ∫ u : ℝ in Set.Ioo (((400 : ℝ) + (j : ℝ)) / 1600) (((400 : ℝ) + (j :
        ℝ) + 1) / 1600),
        u ^ m * hpRiemannThetaDifferentialKernel u) =
      ∫ u : ℝ in Set.Ioo (20 / 80 : ℝ) ((20 + 1) / 80 : ℝ), u ^ m *
        hpRiemannThetaDifferentialKernel u := by
    have h := hpThetaJensen_batchCellIntegral_sum m hm 20
    have hc : ∀ j : ℕ,
        Set.Ioo (((400 : ℝ) + (j : ℝ)) / 1600) (((400 : ℝ) + (j : ℝ) + 1) / 1600) =
          Set.Ioo ((20 : ℝ) / 80 + (j : ℝ) / 1600)
            ((20 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600) := by
      intro j
      have hl : (((400 : ℝ) + (j : ℝ)) / 1600) = (20 : ℝ) / 80 + (j : ℝ) / 1600 := by ring
      have hr : (((400 : ℝ) + (j : ℝ) + 1) / 1600) = (20 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600 :=
        by
        push_cast
        ring
      rw [hl, hr]
    simp_rw [hc]
    exact h
  have h0 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((400 : ℝ) + (j : ℝ)) / 1600) (((400 : ℝ) + (j : ℝ) + 1) / 1600), u ^ 0
        * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((400 : ℝ) + (j : ℝ) + 1) / 1600) ^ 0 *
        hpThetaJensenCellsBatch020Upper j * ((((400 : ℝ) + (j : ℝ) + 1) / 1600) - (((400 : ℝ) + (j
        : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch020_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 0
      (Or.inl rfl)).2
  have h2 : (∑ j ∈ Finset.range 20, (((400 : ℝ) + (j : ℝ)) / 1600) ^ 2 *
    hpThetaJensenCellsBatch020Lower j * ((((400 : ℝ) + (j : ℝ) + 1) / 1600) - (((400 : ℝ) + (j :
    ℝ)) / 1600))) ≤
      ∑ j ∈ Finset.range 20,
        ∫ u : ℝ in Set.Ioo (((400 : ℝ) + (j : ℝ)) / 1600) (((400 : ℝ) + (j : ℝ) + 1) / 1600), u ^
          2 * hpRiemannThetaDifferentialKernel u := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch020_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 2
      (Or.inr (Or.inl rfl))).1
  have h4 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((400 : ℝ) + (j : ℝ)) / 1600) (((400 : ℝ) + (j : ℝ) + 1) / 1600), u ^ 4
        * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((400 : ℝ) + (j : ℝ) + 1) / 1600) ^ 4 *
        hpThetaJensenCellsBatch020Upper j * ((((400 : ℝ) + (j : ℝ) + 1) / 1600) - (((400 : ℝ) + (j
        : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch020_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 4
      (Or.inr (Or.inr rfl))).2
  rw [hs 0 (Or.inl rfl)] at h0
  rw [hs 2 (Or.inr (Or.inl rfl))] at h2
  rw [hs 4 (Or.inr (Or.inr rfl))] at h4
  norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch020Lower,
    hpThetaJensenCellsBatch020Upper] at h0 h2 h4
  norm_num [hpThetaJensenBatchZeroUpper, hpThetaJensenBatchSecondLower,
    hpThetaJensenBatchFourthUpper]
  exact ⟨le_trans h0 (by norm_num), le_trans (by norm_num) h2,
    le_trans h4 (by norm_num)⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Twenty rational terms are verified for each of the three moment orders.
theorem hpThetaJensenCellsBatch021_finiteIntegral_bounds :
    (∫ u : ℝ in Set.Ioo (21 / 80 : ℝ) ((21 + 1) / 80 : ℝ), u ^ 0 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchZeroUpper 21 ∧
    hpThetaJensenBatchSecondLower 21 ≤
        (∫ u : ℝ in Set.Ioo (21 / 80 : ℝ) ((21 + 1) / 80 : ℝ), u ^ 2 *
          hpRiemannThetaDifferentialKernel u) ∧
    (∫ u : ℝ in Set.Ioo (21 / 80 : ℝ) ((21 + 1) / 80 : ℝ), u ^ 4 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchFourthUpper 21 := by
  have hs (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
      (∑ j ∈ Finset.range 20, ∫ u : ℝ in Set.Ioo (((420 : ℝ) + (j : ℝ)) / 1600) (((420 : ℝ) + (j :
        ℝ) + 1) / 1600),
        u ^ m * hpRiemannThetaDifferentialKernel u) =
      ∫ u : ℝ in Set.Ioo (21 / 80 : ℝ) ((21 + 1) / 80 : ℝ), u ^ m *
        hpRiemannThetaDifferentialKernel u := by
    have h := hpThetaJensen_batchCellIntegral_sum m hm 21
    have hc : ∀ j : ℕ,
        Set.Ioo (((420 : ℝ) + (j : ℝ)) / 1600) (((420 : ℝ) + (j : ℝ) + 1) / 1600) =
          Set.Ioo ((21 : ℝ) / 80 + (j : ℝ) / 1600)
            ((21 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600) := by
      intro j
      have hl : (((420 : ℝ) + (j : ℝ)) / 1600) = (21 : ℝ) / 80 + (j : ℝ) / 1600 := by ring
      have hr : (((420 : ℝ) + (j : ℝ) + 1) / 1600) = (21 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600 :=
        by
        push_cast
        ring
      rw [hl, hr]
    simp_rw [hc]
    exact h
  have h0 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((420 : ℝ) + (j : ℝ)) / 1600) (((420 : ℝ) + (j : ℝ) + 1) / 1600), u ^ 0
        * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((420 : ℝ) + (j : ℝ) + 1) / 1600) ^ 0 *
        hpThetaJensenCellsBatch021Upper j * ((((420 : ℝ) + (j : ℝ) + 1) / 1600) - (((420 : ℝ) + (j
        : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch021_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 0
      (Or.inl rfl)).2
  have h2 : (∑ j ∈ Finset.range 20, (((420 : ℝ) + (j : ℝ)) / 1600) ^ 2 *
    hpThetaJensenCellsBatch021Lower j * ((((420 : ℝ) + (j : ℝ) + 1) / 1600) - (((420 : ℝ) + (j :
    ℝ)) / 1600))) ≤
      ∑ j ∈ Finset.range 20,
        ∫ u : ℝ in Set.Ioo (((420 : ℝ) + (j : ℝ)) / 1600) (((420 : ℝ) + (j : ℝ) + 1) / 1600), u ^
          2 * hpRiemannThetaDifferentialKernel u := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch021_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 2
      (Or.inr (Or.inl rfl))).1
  have h4 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((420 : ℝ) + (j : ℝ)) / 1600) (((420 : ℝ) + (j : ℝ) + 1) / 1600), u ^ 4
        * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((420 : ℝ) + (j : ℝ) + 1) / 1600) ^ 4 *
        hpThetaJensenCellsBatch021Upper j * ((((420 : ℝ) + (j : ℝ) + 1) / 1600) - (((420 : ℝ) + (j
        : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch021_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 4
      (Or.inr (Or.inr rfl))).2
  rw [hs 0 (Or.inl rfl)] at h0
  rw [hs 2 (Or.inr (Or.inl rfl))] at h2
  rw [hs 4 (Or.inr (Or.inr rfl))] at h4
  norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch021Lower,
    hpThetaJensenCellsBatch021Upper] at h0 h2 h4
  norm_num [hpThetaJensenBatchZeroUpper, hpThetaJensenBatchSecondLower,
    hpThetaJensenBatchFourthUpper]
  exact ⟨le_trans h0 (by norm_num), le_trans (by norm_num) h2,
    le_trans h4 (by norm_num)⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Twenty rational terms are verified for each of the three moment orders.
theorem hpThetaJensenCellsBatch022_finiteIntegral_bounds :
    (∫ u : ℝ in Set.Ioo (22 / 80 : ℝ) ((22 + 1) / 80 : ℝ), u ^ 0 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchZeroUpper 22 ∧
    hpThetaJensenBatchSecondLower 22 ≤
        (∫ u : ℝ in Set.Ioo (22 / 80 : ℝ) ((22 + 1) / 80 : ℝ), u ^ 2 *
          hpRiemannThetaDifferentialKernel u) ∧
    (∫ u : ℝ in Set.Ioo (22 / 80 : ℝ) ((22 + 1) / 80 : ℝ), u ^ 4 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchFourthUpper 22 := by
  have hs (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
      (∑ j ∈ Finset.range 20, ∫ u : ℝ in Set.Ioo (((440 : ℝ) + (j : ℝ)) / 1600) (((440 : ℝ) + (j :
        ℝ) + 1) / 1600),
        u ^ m * hpRiemannThetaDifferentialKernel u) =
      ∫ u : ℝ in Set.Ioo (22 / 80 : ℝ) ((22 + 1) / 80 : ℝ), u ^ m *
        hpRiemannThetaDifferentialKernel u := by
    have h := hpThetaJensen_batchCellIntegral_sum m hm 22
    have hc : ∀ j : ℕ,
        Set.Ioo (((440 : ℝ) + (j : ℝ)) / 1600) (((440 : ℝ) + (j : ℝ) + 1) / 1600) =
          Set.Ioo ((22 : ℝ) / 80 + (j : ℝ) / 1600)
            ((22 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600) := by
      intro j
      have hl : (((440 : ℝ) + (j : ℝ)) / 1600) = (22 : ℝ) / 80 + (j : ℝ) / 1600 := by ring
      have hr : (((440 : ℝ) + (j : ℝ) + 1) / 1600) = (22 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600 :=
        by
        push_cast
        ring
      rw [hl, hr]
    simp_rw [hc]
    exact h
  have h0 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((440 : ℝ) + (j : ℝ)) / 1600) (((440 : ℝ) + (j : ℝ) + 1) / 1600), u ^ 0
        * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((440 : ℝ) + (j : ℝ) + 1) / 1600) ^ 0 *
        hpThetaJensenCellsBatch022Upper j * ((((440 : ℝ) + (j : ℝ) + 1) / 1600) - (((440 : ℝ) + (j
        : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch022_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 0
      (Or.inl rfl)).2
  have h2 : (∑ j ∈ Finset.range 20, (((440 : ℝ) + (j : ℝ)) / 1600) ^ 2 *
    hpThetaJensenCellsBatch022Lower j * ((((440 : ℝ) + (j : ℝ) + 1) / 1600) - (((440 : ℝ) + (j :
    ℝ)) / 1600))) ≤
      ∑ j ∈ Finset.range 20,
        ∫ u : ℝ in Set.Ioo (((440 : ℝ) + (j : ℝ)) / 1600) (((440 : ℝ) + (j : ℝ) + 1) / 1600), u ^
          2 * hpRiemannThetaDifferentialKernel u := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch022_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 2
      (Or.inr (Or.inl rfl))).1
  have h4 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((440 : ℝ) + (j : ℝ)) / 1600) (((440 : ℝ) + (j : ℝ) + 1) / 1600), u ^ 4
        * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((440 : ℝ) + (j : ℝ) + 1) / 1600) ^ 4 *
        hpThetaJensenCellsBatch022Upper j * ((((440 : ℝ) + (j : ℝ) + 1) / 1600) - (((440 : ℝ) + (j
        : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch022_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 4
      (Or.inr (Or.inr rfl))).2
  rw [hs 0 (Or.inl rfl)] at h0
  rw [hs 2 (Or.inr (Or.inl rfl))] at h2
  rw [hs 4 (Or.inr (Or.inr rfl))] at h4
  norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch022Lower,
    hpThetaJensenCellsBatch022Upper] at h0 h2 h4
  norm_num [hpThetaJensenBatchZeroUpper, hpThetaJensenBatchSecondLower,
    hpThetaJensenBatchFourthUpper]
  exact ⟨le_trans h0 (by norm_num), le_trans (by norm_num) h2,
    le_trans h4 (by norm_num)⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Twenty rational terms are verified for each of the three moment orders.
theorem hpThetaJensenCellsBatch023_finiteIntegral_bounds :
    (∫ u : ℝ in Set.Ioo (23 / 80 : ℝ) ((23 + 1) / 80 : ℝ), u ^ 0 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchZeroUpper 23 ∧
    hpThetaJensenBatchSecondLower 23 ≤
        (∫ u : ℝ in Set.Ioo (23 / 80 : ℝ) ((23 + 1) / 80 : ℝ), u ^ 2 *
          hpRiemannThetaDifferentialKernel u) ∧
    (∫ u : ℝ in Set.Ioo (23 / 80 : ℝ) ((23 + 1) / 80 : ℝ), u ^ 4 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchFourthUpper 23 := by
  have hs (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
      (∑ j ∈ Finset.range 20, ∫ u : ℝ in Set.Ioo (((460 : ℝ) + (j : ℝ)) / 1600) (((460 : ℝ) + (j :
        ℝ) + 1) / 1600),
        u ^ m * hpRiemannThetaDifferentialKernel u) =
      ∫ u : ℝ in Set.Ioo (23 / 80 : ℝ) ((23 + 1) / 80 : ℝ), u ^ m *
        hpRiemannThetaDifferentialKernel u := by
    have h := hpThetaJensen_batchCellIntegral_sum m hm 23
    have hc : ∀ j : ℕ,
        Set.Ioo (((460 : ℝ) + (j : ℝ)) / 1600) (((460 : ℝ) + (j : ℝ) + 1) / 1600) =
          Set.Ioo ((23 : ℝ) / 80 + (j : ℝ) / 1600)
            ((23 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600) := by
      intro j
      have hl : (((460 : ℝ) + (j : ℝ)) / 1600) = (23 : ℝ) / 80 + (j : ℝ) / 1600 := by ring
      have hr : (((460 : ℝ) + (j : ℝ) + 1) / 1600) = (23 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600 :=
        by
        push_cast
        ring
      rw [hl, hr]
    simp_rw [hc]
    exact h
  have h0 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((460 : ℝ) + (j : ℝ)) / 1600) (((460 : ℝ) + (j : ℝ) + 1) / 1600), u ^ 0
        * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((460 : ℝ) + (j : ℝ) + 1) / 1600) ^ 0 *
        hpThetaJensenCellsBatch023Upper j * ((((460 : ℝ) + (j : ℝ) + 1) / 1600) - (((460 : ℝ) + (j
        : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch023_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 0
      (Or.inl rfl)).2
  have h2 : (∑ j ∈ Finset.range 20, (((460 : ℝ) + (j : ℝ)) / 1600) ^ 2 *
    hpThetaJensenCellsBatch023Lower j * ((((460 : ℝ) + (j : ℝ) + 1) / 1600) - (((460 : ℝ) + (j :
    ℝ)) / 1600))) ≤
      ∑ j ∈ Finset.range 20,
        ∫ u : ℝ in Set.Ioo (((460 : ℝ) + (j : ℝ)) / 1600) (((460 : ℝ) + (j : ℝ) + 1) / 1600), u ^
          2 * hpRiemannThetaDifferentialKernel u := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch023_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 2
      (Or.inr (Or.inl rfl))).1
  have h4 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((460 : ℝ) + (j : ℝ)) / 1600) (((460 : ℝ) + (j : ℝ) + 1) / 1600), u ^ 4
        * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((460 : ℝ) + (j : ℝ) + 1) / 1600) ^ 4 *
        hpThetaJensenCellsBatch023Upper j * ((((460 : ℝ) + (j : ℝ) + 1) / 1600) - (((460 : ℝ) + (j
        : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch023_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 4
      (Or.inr (Or.inr rfl))).2
  rw [hs 0 (Or.inl rfl)] at h0
  rw [hs 2 (Or.inr (Or.inl rfl))] at h2
  rw [hs 4 (Or.inr (Or.inr rfl))] at h4
  norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch023Lower,
    hpThetaJensenCellsBatch023Upper] at h0 h2 h4
  norm_num [hpThetaJensenBatchZeroUpper, hpThetaJensenBatchSecondLower,
    hpThetaJensenBatchFourthUpper]
  exact ⟨le_trans h0 (by norm_num), le_trans (by norm_num) h2,
    le_trans h4 (by norm_num)⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Twenty rational terms are verified for each of the three moment orders.
theorem hpThetaJensenCellsBatch024_finiteIntegral_bounds :
    (∫ u : ℝ in Set.Ioo (24 / 80 : ℝ) ((24 + 1) / 80 : ℝ), u ^ 0 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchZeroUpper 24 ∧
    hpThetaJensenBatchSecondLower 24 ≤
        (∫ u : ℝ in Set.Ioo (24 / 80 : ℝ) ((24 + 1) / 80 : ℝ), u ^ 2 *
          hpRiemannThetaDifferentialKernel u) ∧
    (∫ u : ℝ in Set.Ioo (24 / 80 : ℝ) ((24 + 1) / 80 : ℝ), u ^ 4 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchFourthUpper 24 := by
  have hs (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
      (∑ j ∈ Finset.range 20, ∫ u : ℝ in Set.Ioo (((480 : ℝ) + (j : ℝ)) / 1600) (((480 : ℝ) + (j :
        ℝ) + 1) / 1600),
        u ^ m * hpRiemannThetaDifferentialKernel u) =
      ∫ u : ℝ in Set.Ioo (24 / 80 : ℝ) ((24 + 1) / 80 : ℝ), u ^ m *
        hpRiemannThetaDifferentialKernel u := by
    have h := hpThetaJensen_batchCellIntegral_sum m hm 24
    have hc : ∀ j : ℕ,
        Set.Ioo (((480 : ℝ) + (j : ℝ)) / 1600) (((480 : ℝ) + (j : ℝ) + 1) / 1600) =
          Set.Ioo ((24 : ℝ) / 80 + (j : ℝ) / 1600)
            ((24 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600) := by
      intro j
      have hl : (((480 : ℝ) + (j : ℝ)) / 1600) = (24 : ℝ) / 80 + (j : ℝ) / 1600 := by ring
      have hr : (((480 : ℝ) + (j : ℝ) + 1) / 1600) = (24 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600 :=
        by
        push_cast
        ring
      rw [hl, hr]
    simp_rw [hc]
    exact h
  have h0 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((480 : ℝ) + (j : ℝ)) / 1600) (((480 : ℝ) + (j : ℝ) + 1) / 1600), u ^ 0
        * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((480 : ℝ) + (j : ℝ) + 1) / 1600) ^ 0 *
        hpThetaJensenCellsBatch024Upper j * ((((480 : ℝ) + (j : ℝ) + 1) / 1600) - (((480 : ℝ) + (j
        : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch024_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 0
      (Or.inl rfl)).2
  have h2 : (∑ j ∈ Finset.range 20, (((480 : ℝ) + (j : ℝ)) / 1600) ^ 2 *
    hpThetaJensenCellsBatch024Lower j * ((((480 : ℝ) + (j : ℝ) + 1) / 1600) - (((480 : ℝ) + (j :
    ℝ)) / 1600))) ≤
      ∑ j ∈ Finset.range 20,
        ∫ u : ℝ in Set.Ioo (((480 : ℝ) + (j : ℝ)) / 1600) (((480 : ℝ) + (j : ℝ) + 1) / 1600), u ^
          2 * hpRiemannThetaDifferentialKernel u := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch024_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 2
      (Or.inr (Or.inl rfl))).1
  have h4 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((480 : ℝ) + (j : ℝ)) / 1600) (((480 : ℝ) + (j : ℝ) + 1) / 1600), u ^ 4
        * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((480 : ℝ) + (j : ℝ) + 1) / 1600) ^ 4 *
        hpThetaJensenCellsBatch024Upper j * ((((480 : ℝ) + (j : ℝ) + 1) / 1600) - (((480 : ℝ) + (j
        : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch024_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 4
      (Or.inr (Or.inr rfl))).2
  rw [hs 0 (Or.inl rfl)] at h0
  rw [hs 2 (Or.inr (Or.inl rfl))] at h2
  rw [hs 4 (Or.inr (Or.inr rfl))] at h4
  norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch024Lower,
    hpThetaJensenCellsBatch024Upper] at h0 h2 h4
  norm_num [hpThetaJensenBatchZeroUpper, hpThetaJensenBatchSecondLower,
    hpThetaJensenBatchFourthUpper]
  exact ⟨le_trans h0 (by norm_num), le_trans (by norm_num) h2,
    le_trans h4 (by norm_num)⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Twenty rational terms are verified for each of the three moment orders.
theorem hpThetaJensenCellsBatch025_finiteIntegral_bounds :
    (∫ u : ℝ in Set.Ioo (25 / 80 : ℝ) ((25 + 1) / 80 : ℝ), u ^ 0 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchZeroUpper 25 ∧
    hpThetaJensenBatchSecondLower 25 ≤
        (∫ u : ℝ in Set.Ioo (25 / 80 : ℝ) ((25 + 1) / 80 : ℝ), u ^ 2 *
          hpRiemannThetaDifferentialKernel u) ∧
    (∫ u : ℝ in Set.Ioo (25 / 80 : ℝ) ((25 + 1) / 80 : ℝ), u ^ 4 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchFourthUpper 25 := by
  have hs (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
      (∑ j ∈ Finset.range 20, ∫ u : ℝ in Set.Ioo (((500 : ℝ) + (j : ℝ)) / 1600) (((500 : ℝ) + (j :
        ℝ) + 1) / 1600),
        u ^ m * hpRiemannThetaDifferentialKernel u) =
      ∫ u : ℝ in Set.Ioo (25 / 80 : ℝ) ((25 + 1) / 80 : ℝ), u ^ m *
        hpRiemannThetaDifferentialKernel u := by
    have h := hpThetaJensen_batchCellIntegral_sum m hm 25
    have hc : ∀ j : ℕ,
        Set.Ioo (((500 : ℝ) + (j : ℝ)) / 1600) (((500 : ℝ) + (j : ℝ) + 1) / 1600) =
          Set.Ioo ((25 : ℝ) / 80 + (j : ℝ) / 1600)
            ((25 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600) := by
      intro j
      have hl : (((500 : ℝ) + (j : ℝ)) / 1600) = (25 : ℝ) / 80 + (j : ℝ) / 1600 := by ring
      have hr : (((500 : ℝ) + (j : ℝ) + 1) / 1600) = (25 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600 :=
        by
        push_cast
        ring
      rw [hl, hr]
    simp_rw [hc]
    exact h
  have h0 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((500 : ℝ) + (j : ℝ)) / 1600) (((500 : ℝ) + (j : ℝ) + 1) / 1600), u ^ 0
        * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((500 : ℝ) + (j : ℝ) + 1) / 1600) ^ 0 *
        hpThetaJensenCellsBatch025Upper j * ((((500 : ℝ) + (j : ℝ) + 1) / 1600) - (((500 : ℝ) + (j
        : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch025_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 0
      (Or.inl rfl)).2
  have h2 : (∑ j ∈ Finset.range 20, (((500 : ℝ) + (j : ℝ)) / 1600) ^ 2 *
    hpThetaJensenCellsBatch025Lower j * ((((500 : ℝ) + (j : ℝ) + 1) / 1600) - (((500 : ℝ) + (j :
    ℝ)) / 1600))) ≤
      ∑ j ∈ Finset.range 20,
        ∫ u : ℝ in Set.Ioo (((500 : ℝ) + (j : ℝ)) / 1600) (((500 : ℝ) + (j : ℝ) + 1) / 1600), u ^
          2 * hpRiemannThetaDifferentialKernel u := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch025_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 2
      (Or.inr (Or.inl rfl))).1
  have h4 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((500 : ℝ) + (j : ℝ)) / 1600) (((500 : ℝ) + (j : ℝ) + 1) / 1600), u ^ 4
        * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((500 : ℝ) + (j : ℝ) + 1) / 1600) ^ 4 *
        hpThetaJensenCellsBatch025Upper j * ((((500 : ℝ) + (j : ℝ) + 1) / 1600) - (((500 : ℝ) + (j
        : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch025_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 4
      (Or.inr (Or.inr rfl))).2
  rw [hs 0 (Or.inl rfl)] at h0
  rw [hs 2 (Or.inr (Or.inl rfl))] at h2
  rw [hs 4 (Or.inr (Or.inr rfl))] at h4
  norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch025Lower,
    hpThetaJensenCellsBatch025Upper] at h0 h2 h4
  norm_num [hpThetaJensenBatchZeroUpper, hpThetaJensenBatchSecondLower,
    hpThetaJensenBatchFourthUpper]
  exact ⟨le_trans h0 (by norm_num), le_trans (by norm_num) h2,
    le_trans h4 (by norm_num)⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Twenty rational terms are verified for each of the three moment orders.
theorem hpThetaJensenCellsBatch026_finiteIntegral_bounds :
    (∫ u : ℝ in Set.Ioo (26 / 80 : ℝ) ((26 + 1) / 80 : ℝ), u ^ 0 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchZeroUpper 26 ∧
    hpThetaJensenBatchSecondLower 26 ≤
        (∫ u : ℝ in Set.Ioo (26 / 80 : ℝ) ((26 + 1) / 80 : ℝ), u ^ 2 *
          hpRiemannThetaDifferentialKernel u) ∧
    (∫ u : ℝ in Set.Ioo (26 / 80 : ℝ) ((26 + 1) / 80 : ℝ), u ^ 4 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchFourthUpper 26 := by
  have hs (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
      (∑ j ∈ Finset.range 20, ∫ u : ℝ in Set.Ioo (((520 : ℝ) + (j : ℝ)) / 1600) (((520 : ℝ) + (j :
        ℝ) + 1) / 1600),
        u ^ m * hpRiemannThetaDifferentialKernel u) =
      ∫ u : ℝ in Set.Ioo (26 / 80 : ℝ) ((26 + 1) / 80 : ℝ), u ^ m *
        hpRiemannThetaDifferentialKernel u := by
    have h := hpThetaJensen_batchCellIntegral_sum m hm 26
    have hc : ∀ j : ℕ,
        Set.Ioo (((520 : ℝ) + (j : ℝ)) / 1600) (((520 : ℝ) + (j : ℝ) + 1) / 1600) =
          Set.Ioo ((26 : ℝ) / 80 + (j : ℝ) / 1600)
            ((26 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600) := by
      intro j
      have hl : (((520 : ℝ) + (j : ℝ)) / 1600) = (26 : ℝ) / 80 + (j : ℝ) / 1600 := by ring
      have hr : (((520 : ℝ) + (j : ℝ) + 1) / 1600) = (26 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600 :=
        by
        push_cast
        ring
      rw [hl, hr]
    simp_rw [hc]
    exact h
  have h0 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((520 : ℝ) + (j : ℝ)) / 1600) (((520 : ℝ) + (j : ℝ) + 1) / 1600), u ^ 0
        * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((520 : ℝ) + (j : ℝ) + 1) / 1600) ^ 0 *
        hpThetaJensenCellsBatch026Upper j * ((((520 : ℝ) + (j : ℝ) + 1) / 1600) - (((520 : ℝ) + (j
        : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch026_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 0
      (Or.inl rfl)).2
  have h2 : (∑ j ∈ Finset.range 20, (((520 : ℝ) + (j : ℝ)) / 1600) ^ 2 *
    hpThetaJensenCellsBatch026Lower j * ((((520 : ℝ) + (j : ℝ) + 1) / 1600) - (((520 : ℝ) + (j :
    ℝ)) / 1600))) ≤
      ∑ j ∈ Finset.range 20,
        ∫ u : ℝ in Set.Ioo (((520 : ℝ) + (j : ℝ)) / 1600) (((520 : ℝ) + (j : ℝ) + 1) / 1600), u ^
          2 * hpRiemannThetaDifferentialKernel u := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch026_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 2
      (Or.inr (Or.inl rfl))).1
  have h4 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((520 : ℝ) + (j : ℝ)) / 1600) (((520 : ℝ) + (j : ℝ) + 1) / 1600), u ^ 4
        * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((520 : ℝ) + (j : ℝ) + 1) / 1600) ^ 4 *
        hpThetaJensenCellsBatch026Upper j * ((((520 : ℝ) + (j : ℝ) + 1) / 1600) - (((520 : ℝ) + (j
        : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch026_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 4
      (Or.inr (Or.inr rfl))).2
  rw [hs 0 (Or.inl rfl)] at h0
  rw [hs 2 (Or.inr (Or.inl rfl))] at h2
  rw [hs 4 (Or.inr (Or.inr rfl))] at h4
  norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch026Lower,
    hpThetaJensenCellsBatch026Upper] at h0 h2 h4
  norm_num [hpThetaJensenBatchZeroUpper, hpThetaJensenBatchSecondLower,
    hpThetaJensenBatchFourthUpper]
  exact ⟨le_trans h0 (by norm_num), le_trans (by norm_num) h2,
    le_trans h4 (by norm_num)⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Twenty rational terms are verified for each of the three moment orders.
theorem hpThetaJensenCellsBatch027_finiteIntegral_bounds :
    (∫ u : ℝ in Set.Ioo (27 / 80 : ℝ) ((27 + 1) / 80 : ℝ), u ^ 0 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchZeroUpper 27 ∧
    hpThetaJensenBatchSecondLower 27 ≤
        (∫ u : ℝ in Set.Ioo (27 / 80 : ℝ) ((27 + 1) / 80 : ℝ), u ^ 2 *
          hpRiemannThetaDifferentialKernel u) ∧
    (∫ u : ℝ in Set.Ioo (27 / 80 : ℝ) ((27 + 1) / 80 : ℝ), u ^ 4 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchFourthUpper 27 := by
  have hs (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
      (∑ j ∈ Finset.range 20, ∫ u : ℝ in Set.Ioo (((540 : ℝ) + (j : ℝ)) / 1600) (((540 : ℝ) + (j :
        ℝ) + 1) / 1600),
        u ^ m * hpRiemannThetaDifferentialKernel u) =
      ∫ u : ℝ in Set.Ioo (27 / 80 : ℝ) ((27 + 1) / 80 : ℝ), u ^ m *
        hpRiemannThetaDifferentialKernel u := by
    have h := hpThetaJensen_batchCellIntegral_sum m hm 27
    have hc : ∀ j : ℕ,
        Set.Ioo (((540 : ℝ) + (j : ℝ)) / 1600) (((540 : ℝ) + (j : ℝ) + 1) / 1600) =
          Set.Ioo ((27 : ℝ) / 80 + (j : ℝ) / 1600)
            ((27 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600) := by
      intro j
      have hl : (((540 : ℝ) + (j : ℝ)) / 1600) = (27 : ℝ) / 80 + (j : ℝ) / 1600 := by ring
      have hr : (((540 : ℝ) + (j : ℝ) + 1) / 1600) = (27 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600 :=
        by
        push_cast
        ring
      rw [hl, hr]
    simp_rw [hc]
    exact h
  have h0 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((540 : ℝ) + (j : ℝ)) / 1600) (((540 : ℝ) + (j : ℝ) + 1) / 1600), u ^ 0
        * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((540 : ℝ) + (j : ℝ) + 1) / 1600) ^ 0 *
        hpThetaJensenCellsBatch027Upper j * ((((540 : ℝ) + (j : ℝ) + 1) / 1600) - (((540 : ℝ) + (j
        : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch027_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 0
      (Or.inl rfl)).2
  have h2 : (∑ j ∈ Finset.range 20, (((540 : ℝ) + (j : ℝ)) / 1600) ^ 2 *
    hpThetaJensenCellsBatch027Lower j * ((((540 : ℝ) + (j : ℝ) + 1) / 1600) - (((540 : ℝ) + (j :
    ℝ)) / 1600))) ≤
      ∑ j ∈ Finset.range 20,
        ∫ u : ℝ in Set.Ioo (((540 : ℝ) + (j : ℝ)) / 1600) (((540 : ℝ) + (j : ℝ) + 1) / 1600), u ^
          2 * hpRiemannThetaDifferentialKernel u := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch027_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 2
      (Or.inr (Or.inl rfl))).1
  have h4 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((540 : ℝ) + (j : ℝ)) / 1600) (((540 : ℝ) + (j : ℝ) + 1) / 1600), u ^ 4
        * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((540 : ℝ) + (j : ℝ) + 1) / 1600) ^ 4 *
        hpThetaJensenCellsBatch027Upper j * ((((540 : ℝ) + (j : ℝ) + 1) / 1600) - (((540 : ℝ) + (j
        : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch027_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 4
      (Or.inr (Or.inr rfl))).2
  rw [hs 0 (Or.inl rfl)] at h0
  rw [hs 2 (Or.inr (Or.inl rfl))] at h2
  rw [hs 4 (Or.inr (Or.inr rfl))] at h4
  norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch027Lower,
    hpThetaJensenCellsBatch027Upper] at h0 h2 h4
  norm_num [hpThetaJensenBatchZeroUpper, hpThetaJensenBatchSecondLower,
    hpThetaJensenBatchFourthUpper]
  exact ⟨le_trans h0 (by norm_num), le_trans (by norm_num) h2,
    le_trans h4 (by norm_num)⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Twenty rational terms are verified for each of the three moment orders.
theorem hpThetaJensenCellsBatch028_finiteIntegral_bounds :
    (∫ u : ℝ in Set.Ioo (28 / 80 : ℝ) ((28 + 1) / 80 : ℝ), u ^ 0 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchZeroUpper 28 ∧
    hpThetaJensenBatchSecondLower 28 ≤
        (∫ u : ℝ in Set.Ioo (28 / 80 : ℝ) ((28 + 1) / 80 : ℝ), u ^ 2 *
          hpRiemannThetaDifferentialKernel u) ∧
    (∫ u : ℝ in Set.Ioo (28 / 80 : ℝ) ((28 + 1) / 80 : ℝ), u ^ 4 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchFourthUpper 28 := by
  have hs (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
      (∑ j ∈ Finset.range 20, ∫ u : ℝ in Set.Ioo (((560 : ℝ) + (j : ℝ)) / 1600) (((560 : ℝ) + (j :
        ℝ) + 1) / 1600),
        u ^ m * hpRiemannThetaDifferentialKernel u) =
      ∫ u : ℝ in Set.Ioo (28 / 80 : ℝ) ((28 + 1) / 80 : ℝ), u ^ m *
        hpRiemannThetaDifferentialKernel u := by
    have h := hpThetaJensen_batchCellIntegral_sum m hm 28
    have hc : ∀ j : ℕ,
        Set.Ioo (((560 : ℝ) + (j : ℝ)) / 1600) (((560 : ℝ) + (j : ℝ) + 1) / 1600) =
          Set.Ioo ((28 : ℝ) / 80 + (j : ℝ) / 1600)
            ((28 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600) := by
      intro j
      have hl : (((560 : ℝ) + (j : ℝ)) / 1600) = (28 : ℝ) / 80 + (j : ℝ) / 1600 := by ring
      have hr : (((560 : ℝ) + (j : ℝ) + 1) / 1600) = (28 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600 :=
        by
        push_cast
        ring
      rw [hl, hr]
    simp_rw [hc]
    exact h
  have h0 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((560 : ℝ) + (j : ℝ)) / 1600) (((560 : ℝ) + (j : ℝ) + 1) / 1600), u ^ 0
        * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((560 : ℝ) + (j : ℝ) + 1) / 1600) ^ 0 *
        hpThetaJensenCellsBatch028Upper j * ((((560 : ℝ) + (j : ℝ) + 1) / 1600) - (((560 : ℝ) + (j
        : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch028_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 0
      (Or.inl rfl)).2
  have h2 : (∑ j ∈ Finset.range 20, (((560 : ℝ) + (j : ℝ)) / 1600) ^ 2 *
    hpThetaJensenCellsBatch028Lower j * ((((560 : ℝ) + (j : ℝ) + 1) / 1600) - (((560 : ℝ) + (j :
    ℝ)) / 1600))) ≤
      ∑ j ∈ Finset.range 20,
        ∫ u : ℝ in Set.Ioo (((560 : ℝ) + (j : ℝ)) / 1600) (((560 : ℝ) + (j : ℝ) + 1) / 1600), u ^
          2 * hpRiemannThetaDifferentialKernel u := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch028_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 2
      (Or.inr (Or.inl rfl))).1
  have h4 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((560 : ℝ) + (j : ℝ)) / 1600) (((560 : ℝ) + (j : ℝ) + 1) / 1600), u ^ 4
        * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((560 : ℝ) + (j : ℝ) + 1) / 1600) ^ 4 *
        hpThetaJensenCellsBatch028Upper j * ((((560 : ℝ) + (j : ℝ) + 1) / 1600) - (((560 : ℝ) + (j
        : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch028_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 4
      (Or.inr (Or.inr rfl))).2
  rw [hs 0 (Or.inl rfl)] at h0
  rw [hs 2 (Or.inr (Or.inl rfl))] at h2
  rw [hs 4 (Or.inr (Or.inr rfl))] at h4
  norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch028Lower,
    hpThetaJensenCellsBatch028Upper] at h0 h2 h4
  norm_num [hpThetaJensenBatchZeroUpper, hpThetaJensenBatchSecondLower,
    hpThetaJensenBatchFourthUpper]
  exact ⟨le_trans h0 (by norm_num), le_trans (by norm_num) h2,
    le_trans h4 (by norm_num)⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Twenty rational terms are verified for each of the three moment orders.
theorem hpThetaJensenCellsBatch029_finiteIntegral_bounds :
    (∫ u : ℝ in Set.Ioo (29 / 80 : ℝ) ((29 + 1) / 80 : ℝ), u ^ 0 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchZeroUpper 29 ∧
    hpThetaJensenBatchSecondLower 29 ≤
        (∫ u : ℝ in Set.Ioo (29 / 80 : ℝ) ((29 + 1) / 80 : ℝ), u ^ 2 *
          hpRiemannThetaDifferentialKernel u) ∧
    (∫ u : ℝ in Set.Ioo (29 / 80 : ℝ) ((29 + 1) / 80 : ℝ), u ^ 4 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchFourthUpper 29 := by
  have hs (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
      (∑ j ∈ Finset.range 20, ∫ u : ℝ in Set.Ioo (((580 : ℝ) + (j : ℝ)) / 1600) (((580 : ℝ) + (j :
        ℝ) + 1) / 1600),
        u ^ m * hpRiemannThetaDifferentialKernel u) =
      ∫ u : ℝ in Set.Ioo (29 / 80 : ℝ) ((29 + 1) / 80 : ℝ), u ^ m *
        hpRiemannThetaDifferentialKernel u := by
    have h := hpThetaJensen_batchCellIntegral_sum m hm 29
    have hc : ∀ j : ℕ,
        Set.Ioo (((580 : ℝ) + (j : ℝ)) / 1600) (((580 : ℝ) + (j : ℝ) + 1) / 1600) =
          Set.Ioo ((29 : ℝ) / 80 + (j : ℝ) / 1600)
            ((29 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600) := by
      intro j
      have hl : (((580 : ℝ) + (j : ℝ)) / 1600) = (29 : ℝ) / 80 + (j : ℝ) / 1600 := by ring
      have hr : (((580 : ℝ) + (j : ℝ) + 1) / 1600) = (29 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600 :=
        by
        push_cast
        ring
      rw [hl, hr]
    simp_rw [hc]
    exact h
  have h0 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((580 : ℝ) + (j : ℝ)) / 1600) (((580 : ℝ) + (j : ℝ) + 1) / 1600), u ^ 0
        * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((580 : ℝ) + (j : ℝ) + 1) / 1600) ^ 0 *
        hpThetaJensenCellsBatch029Upper j * ((((580 : ℝ) + (j : ℝ) + 1) / 1600) - (((580 : ℝ) + (j
        : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch029_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 0
      (Or.inl rfl)).2
  have h2 : (∑ j ∈ Finset.range 20, (((580 : ℝ) + (j : ℝ)) / 1600) ^ 2 *
    hpThetaJensenCellsBatch029Lower j * ((((580 : ℝ) + (j : ℝ) + 1) / 1600) - (((580 : ℝ) + (j :
    ℝ)) / 1600))) ≤
      ∑ j ∈ Finset.range 20,
        ∫ u : ℝ in Set.Ioo (((580 : ℝ) + (j : ℝ)) / 1600) (((580 : ℝ) + (j : ℝ) + 1) / 1600), u ^
          2 * hpRiemannThetaDifferentialKernel u := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch029_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 2
      (Or.inr (Or.inl rfl))).1
  have h4 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((580 : ℝ) + (j : ℝ)) / 1600) (((580 : ℝ) + (j : ℝ) + 1) / 1600), u ^ 4
        * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((580 : ℝ) + (j : ℝ) + 1) / 1600) ^ 4 *
        hpThetaJensenCellsBatch029Upper j * ((((580 : ℝ) + (j : ℝ) + 1) / 1600) - (((580 : ℝ) + (j
        : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch029_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 4
      (Or.inr (Or.inr rfl))).2
  rw [hs 0 (Or.inl rfl)] at h0
  rw [hs 2 (Or.inr (Or.inl rfl))] at h2
  rw [hs 4 (Or.inr (Or.inr rfl))] at h4
  norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch029Lower,
    hpThetaJensenCellsBatch029Upper] at h0 h2 h4
  norm_num [hpThetaJensenBatchZeroUpper, hpThetaJensenBatchSecondLower,
    hpThetaJensenBatchFourthUpper]
  exact ⟨le_trans h0 (by norm_num), le_trans (by norm_num) h2,
    le_trans h4 (by norm_num)⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Twenty rational terms are verified for each of the three moment orders.
theorem hpThetaJensenCellsBatch030_finiteIntegral_bounds :
    (∫ u : ℝ in Set.Ioo (30 / 80 : ℝ) ((30 + 1) / 80 : ℝ), u ^ 0 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchZeroUpper 30 ∧
    hpThetaJensenBatchSecondLower 30 ≤
        (∫ u : ℝ in Set.Ioo (30 / 80 : ℝ) ((30 + 1) / 80 : ℝ), u ^ 2 *
          hpRiemannThetaDifferentialKernel u) ∧
    (∫ u : ℝ in Set.Ioo (30 / 80 : ℝ) ((30 + 1) / 80 : ℝ), u ^ 4 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchFourthUpper 30 := by
  have hs (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
      (∑ j ∈ Finset.range 20, ∫ u : ℝ in Set.Ioo (((600 : ℝ) + (j : ℝ)) / 1600) (((600 : ℝ) + (j :
        ℝ) + 1) / 1600),
        u ^ m * hpRiemannThetaDifferentialKernel u) =
      ∫ u : ℝ in Set.Ioo (30 / 80 : ℝ) ((30 + 1) / 80 : ℝ), u ^ m *
        hpRiemannThetaDifferentialKernel u := by
    have h := hpThetaJensen_batchCellIntegral_sum m hm 30
    have hc : ∀ j : ℕ,
        Set.Ioo (((600 : ℝ) + (j : ℝ)) / 1600) (((600 : ℝ) + (j : ℝ) + 1) / 1600) =
          Set.Ioo ((30 : ℝ) / 80 + (j : ℝ) / 1600)
            ((30 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600) := by
      intro j
      have hl : (((600 : ℝ) + (j : ℝ)) / 1600) = (30 : ℝ) / 80 + (j : ℝ) / 1600 := by ring
      have hr : (((600 : ℝ) + (j : ℝ) + 1) / 1600) = (30 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600 :=
        by
        push_cast
        ring
      rw [hl, hr]
    simp_rw [hc]
    exact h
  have h0 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((600 : ℝ) + (j : ℝ)) / 1600) (((600 : ℝ) + (j : ℝ) + 1) / 1600), u ^ 0
        * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((600 : ℝ) + (j : ℝ) + 1) / 1600) ^ 0 *
        hpThetaJensenCellsBatch030Upper j * ((((600 : ℝ) + (j : ℝ) + 1) / 1600) - (((600 : ℝ) + (j
        : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch030_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 0
      (Or.inl rfl)).2
  have h2 : (∑ j ∈ Finset.range 20, (((600 : ℝ) + (j : ℝ)) / 1600) ^ 2 *
    hpThetaJensenCellsBatch030Lower j * ((((600 : ℝ) + (j : ℝ) + 1) / 1600) - (((600 : ℝ) + (j :
    ℝ)) / 1600))) ≤
      ∑ j ∈ Finset.range 20,
        ∫ u : ℝ in Set.Ioo (((600 : ℝ) + (j : ℝ)) / 1600) (((600 : ℝ) + (j : ℝ) + 1) / 1600), u ^
          2 * hpRiemannThetaDifferentialKernel u := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch030_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 2
      (Or.inr (Or.inl rfl))).1
  have h4 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((600 : ℝ) + (j : ℝ)) / 1600) (((600 : ℝ) + (j : ℝ) + 1) / 1600), u ^ 4
        * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((600 : ℝ) + (j : ℝ) + 1) / 1600) ^ 4 *
        hpThetaJensenCellsBatch030Upper j * ((((600 : ℝ) + (j : ℝ) + 1) / 1600) - (((600 : ℝ) + (j
        : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch030_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 4
      (Or.inr (Or.inr rfl))).2
  rw [hs 0 (Or.inl rfl)] at h0
  rw [hs 2 (Or.inr (Or.inl rfl))] at h2
  rw [hs 4 (Or.inr (Or.inr rfl))] at h4
  norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch030Lower,
    hpThetaJensenCellsBatch030Upper] at h0 h2 h4
  norm_num [hpThetaJensenBatchZeroUpper, hpThetaJensenBatchSecondLower,
    hpThetaJensenBatchFourthUpper]
  exact ⟨le_trans h0 (by norm_num), le_trans (by norm_num) h2,
    le_trans h4 (by norm_num)⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Twenty rational terms are verified for each of the three moment orders.
theorem hpThetaJensenCellsBatch031_finiteIntegral_bounds :
    (∫ u : ℝ in Set.Ioo (31 / 80 : ℝ) ((31 + 1) / 80 : ℝ), u ^ 0 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchZeroUpper 31 ∧
    hpThetaJensenBatchSecondLower 31 ≤
        (∫ u : ℝ in Set.Ioo (31 / 80 : ℝ) ((31 + 1) / 80 : ℝ), u ^ 2 *
          hpRiemannThetaDifferentialKernel u) ∧
    (∫ u : ℝ in Set.Ioo (31 / 80 : ℝ) ((31 + 1) / 80 : ℝ), u ^ 4 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchFourthUpper 31 := by
  have hs (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
      (∑ j ∈ Finset.range 20, ∫ u : ℝ in Set.Ioo (((620 : ℝ) + (j : ℝ)) / 1600) (((620 : ℝ) + (j :
        ℝ) + 1) / 1600),
        u ^ m * hpRiemannThetaDifferentialKernel u) =
      ∫ u : ℝ in Set.Ioo (31 / 80 : ℝ) ((31 + 1) / 80 : ℝ), u ^ m *
        hpRiemannThetaDifferentialKernel u := by
    have h := hpThetaJensen_batchCellIntegral_sum m hm 31
    have hc : ∀ j : ℕ,
        Set.Ioo (((620 : ℝ) + (j : ℝ)) / 1600) (((620 : ℝ) + (j : ℝ) + 1) / 1600) =
          Set.Ioo ((31 : ℝ) / 80 + (j : ℝ) / 1600)
            ((31 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600) := by
      intro j
      have hl : (((620 : ℝ) + (j : ℝ)) / 1600) = (31 : ℝ) / 80 + (j : ℝ) / 1600 := by ring
      have hr : (((620 : ℝ) + (j : ℝ) + 1) / 1600) = (31 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600 :=
        by
        push_cast
        ring
      rw [hl, hr]
    simp_rw [hc]
    exact h
  have h0 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((620 : ℝ) + (j : ℝ)) / 1600) (((620 : ℝ) + (j : ℝ) + 1) / 1600), u ^ 0
        * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((620 : ℝ) + (j : ℝ) + 1) / 1600) ^ 0 *
        hpThetaJensenCellsBatch031Upper j * ((((620 : ℝ) + (j : ℝ) + 1) / 1600) - (((620 : ℝ) + (j
        : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch031_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 0
      (Or.inl rfl)).2
  have h2 : (∑ j ∈ Finset.range 20, (((620 : ℝ) + (j : ℝ)) / 1600) ^ 2 *
    hpThetaJensenCellsBatch031Lower j * ((((620 : ℝ) + (j : ℝ) + 1) / 1600) - (((620 : ℝ) + (j :
    ℝ)) / 1600))) ≤
      ∑ j ∈ Finset.range 20,
        ∫ u : ℝ in Set.Ioo (((620 : ℝ) + (j : ℝ)) / 1600) (((620 : ℝ) + (j : ℝ) + 1) / 1600), u ^
          2 * hpRiemannThetaDifferentialKernel u := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch031_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 2
      (Or.inr (Or.inl rfl))).1
  have h4 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((620 : ℝ) + (j : ℝ)) / 1600) (((620 : ℝ) + (j : ℝ) + 1) / 1600), u ^ 4
        * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((620 : ℝ) + (j : ℝ) + 1) / 1600) ^ 4 *
        hpThetaJensenCellsBatch031Upper j * ((((620 : ℝ) + (j : ℝ) + 1) / 1600) - (((620 : ℝ) + (j
        : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch031_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 4
      (Or.inr (Or.inr rfl))).2
  rw [hs 0 (Or.inl rfl)] at h0
  rw [hs 2 (Or.inr (Or.inl rfl))] at h2
  rw [hs 4 (Or.inr (Or.inr rfl))] at h4
  norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch031Lower,
    hpThetaJensenCellsBatch031Upper] at h0 h2 h4
  norm_num [hpThetaJensenBatchZeroUpper, hpThetaJensenBatchSecondLower,
    hpThetaJensenBatchFourthUpper]
  exact ⟨le_trans h0 (by norm_num), le_trans (by norm_num) h2,
    le_trans h4 (by norm_num)⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Twenty rational terms are verified for each of the three moment orders.
theorem hpThetaJensenCellsBatch032_finiteIntegral_bounds :
    (∫ u : ℝ in Set.Ioo (32 / 80 : ℝ) ((32 + 1) / 80 : ℝ), u ^ 0 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchZeroUpper 32 ∧
    hpThetaJensenBatchSecondLower 32 ≤
        (∫ u : ℝ in Set.Ioo (32 / 80 : ℝ) ((32 + 1) / 80 : ℝ), u ^ 2 *
          hpRiemannThetaDifferentialKernel u) ∧
    (∫ u : ℝ in Set.Ioo (32 / 80 : ℝ) ((32 + 1) / 80 : ℝ), u ^ 4 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchFourthUpper 32 := by
  have hs (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
      (∑ j ∈ Finset.range 20, ∫ u : ℝ in Set.Ioo (((640 : ℝ) + (j : ℝ)) / 1600) (((640 : ℝ) + (j :
        ℝ) + 1) / 1600),
        u ^ m * hpRiemannThetaDifferentialKernel u) =
      ∫ u : ℝ in Set.Ioo (32 / 80 : ℝ) ((32 + 1) / 80 : ℝ), u ^ m *
        hpRiemannThetaDifferentialKernel u := by
    have h := hpThetaJensen_batchCellIntegral_sum m hm 32
    have hc : ∀ j : ℕ,
        Set.Ioo (((640 : ℝ) + (j : ℝ)) / 1600) (((640 : ℝ) + (j : ℝ) + 1) / 1600) =
          Set.Ioo ((32 : ℝ) / 80 + (j : ℝ) / 1600)
            ((32 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600) := by
      intro j
      have hl : (((640 : ℝ) + (j : ℝ)) / 1600) = (32 : ℝ) / 80 + (j : ℝ) / 1600 := by ring
      have hr : (((640 : ℝ) + (j : ℝ) + 1) / 1600) = (32 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600 :=
        by
        push_cast
        ring
      rw [hl, hr]
    simp_rw [hc]
    exact h
  have h0 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((640 : ℝ) + (j : ℝ)) / 1600) (((640 : ℝ) + (j : ℝ) + 1) / 1600), u ^ 0
        * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((640 : ℝ) + (j : ℝ) + 1) / 1600) ^ 0 *
        hpThetaJensenCellsBatch032Upper j * ((((640 : ℝ) + (j : ℝ) + 1) / 1600) - (((640 : ℝ) + (j
        : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch032_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 0
      (Or.inl rfl)).2
  have h2 : (∑ j ∈ Finset.range 20, (((640 : ℝ) + (j : ℝ)) / 1600) ^ 2 *
    hpThetaJensenCellsBatch032Lower j * ((((640 : ℝ) + (j : ℝ) + 1) / 1600) - (((640 : ℝ) + (j :
    ℝ)) / 1600))) ≤
      ∑ j ∈ Finset.range 20,
        ∫ u : ℝ in Set.Ioo (((640 : ℝ) + (j : ℝ)) / 1600) (((640 : ℝ) + (j : ℝ) + 1) / 1600), u ^
          2 * hpRiemannThetaDifferentialKernel u := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch032_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 2
      (Or.inr (Or.inl rfl))).1
  have h4 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((640 : ℝ) + (j : ℝ)) / 1600) (((640 : ℝ) + (j : ℝ) + 1) / 1600), u ^ 4
        * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((640 : ℝ) + (j : ℝ) + 1) / 1600) ^ 4 *
        hpThetaJensenCellsBatch032Upper j * ((((640 : ℝ) + (j : ℝ) + 1) / 1600) - (((640 : ℝ) + (j
        : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch032_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 4
      (Or.inr (Or.inr rfl))).2
  rw [hs 0 (Or.inl rfl)] at h0
  rw [hs 2 (Or.inr (Or.inl rfl))] at h2
  rw [hs 4 (Or.inr (Or.inr rfl))] at h4
  norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch032Lower,
    hpThetaJensenCellsBatch032Upper] at h0 h2 h4
  norm_num [hpThetaJensenBatchZeroUpper, hpThetaJensenBatchSecondLower,
    hpThetaJensenBatchFourthUpper]
  exact ⟨le_trans h0 (by norm_num), le_trans (by norm_num) h2,
    le_trans h4 (by norm_num)⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Twenty rational terms are verified for each of the three moment orders.
theorem hpThetaJensenCellsBatch033_finiteIntegral_bounds :
    (∫ u : ℝ in Set.Ioo (33 / 80 : ℝ) ((33 + 1) / 80 : ℝ), u ^ 0 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchZeroUpper 33 ∧
    hpThetaJensenBatchSecondLower 33 ≤
        (∫ u : ℝ in Set.Ioo (33 / 80 : ℝ) ((33 + 1) / 80 : ℝ), u ^ 2 *
          hpRiemannThetaDifferentialKernel u) ∧
    (∫ u : ℝ in Set.Ioo (33 / 80 : ℝ) ((33 + 1) / 80 : ℝ), u ^ 4 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchFourthUpper 33 := by
  have hs (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
      (∑ j ∈ Finset.range 20, ∫ u : ℝ in Set.Ioo (((660 : ℝ) + (j : ℝ)) / 1600) (((660 : ℝ) + (j :
        ℝ) + 1) / 1600),
        u ^ m * hpRiemannThetaDifferentialKernel u) =
      ∫ u : ℝ in Set.Ioo (33 / 80 : ℝ) ((33 + 1) / 80 : ℝ), u ^ m *
        hpRiemannThetaDifferentialKernel u := by
    have h := hpThetaJensen_batchCellIntegral_sum m hm 33
    have hc : ∀ j : ℕ,
        Set.Ioo (((660 : ℝ) + (j : ℝ)) / 1600) (((660 : ℝ) + (j : ℝ) + 1) / 1600) =
          Set.Ioo ((33 : ℝ) / 80 + (j : ℝ) / 1600)
            ((33 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600) := by
      intro j
      have hl : (((660 : ℝ) + (j : ℝ)) / 1600) = (33 : ℝ) / 80 + (j : ℝ) / 1600 := by ring
      have hr : (((660 : ℝ) + (j : ℝ) + 1) / 1600) = (33 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600 :=
        by
        push_cast
        ring
      rw [hl, hr]
    simp_rw [hc]
    exact h
  have h0 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((660 : ℝ) + (j : ℝ)) / 1600) (((660 : ℝ) + (j : ℝ) + 1) / 1600), u ^ 0
        * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((660 : ℝ) + (j : ℝ) + 1) / 1600) ^ 0 *
        hpThetaJensenCellsBatch033Upper j * ((((660 : ℝ) + (j : ℝ) + 1) / 1600) - (((660 : ℝ) + (j
        : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch033_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 0
      (Or.inl rfl)).2
  have h2 : (∑ j ∈ Finset.range 20, (((660 : ℝ) + (j : ℝ)) / 1600) ^ 2 *
    hpThetaJensenCellsBatch033Lower j * ((((660 : ℝ) + (j : ℝ) + 1) / 1600) - (((660 : ℝ) + (j :
    ℝ)) / 1600))) ≤
      ∑ j ∈ Finset.range 20,
        ∫ u : ℝ in Set.Ioo (((660 : ℝ) + (j : ℝ)) / 1600) (((660 : ℝ) + (j : ℝ) + 1) / 1600), u ^
          2 * hpRiemannThetaDifferentialKernel u := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch033_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 2
      (Or.inr (Or.inl rfl))).1
  have h4 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((660 : ℝ) + (j : ℝ)) / 1600) (((660 : ℝ) + (j : ℝ) + 1) / 1600), u ^ 4
        * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((660 : ℝ) + (j : ℝ) + 1) / 1600) ^ 4 *
        hpThetaJensenCellsBatch033Upper j * ((((660 : ℝ) + (j : ℝ) + 1) / 1600) - (((660 : ℝ) + (j
        : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch033_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 4
      (Or.inr (Or.inr rfl))).2
  rw [hs 0 (Or.inl rfl)] at h0
  rw [hs 2 (Or.inr (Or.inl rfl))] at h2
  rw [hs 4 (Or.inr (Or.inr rfl))] at h4
  norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch033Lower,
    hpThetaJensenCellsBatch033Upper] at h0 h2 h4
  norm_num [hpThetaJensenBatchZeroUpper, hpThetaJensenBatchSecondLower,
    hpThetaJensenBatchFourthUpper]
  exact ⟨le_trans h0 (by norm_num), le_trans (by norm_num) h2,
    le_trans h4 (by norm_num)⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Twenty rational terms are verified for each of the three moment orders.
theorem hpThetaJensenCellsBatch034_finiteIntegral_bounds :
    (∫ u : ℝ in Set.Ioo (34 / 80 : ℝ) ((34 + 1) / 80 : ℝ), u ^ 0 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchZeroUpper 34 ∧
    hpThetaJensenBatchSecondLower 34 ≤
        (∫ u : ℝ in Set.Ioo (34 / 80 : ℝ) ((34 + 1) / 80 : ℝ), u ^ 2 *
          hpRiemannThetaDifferentialKernel u) ∧
    (∫ u : ℝ in Set.Ioo (34 / 80 : ℝ) ((34 + 1) / 80 : ℝ), u ^ 4 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchFourthUpper 34 := by
  have hs (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
      (∑ j ∈ Finset.range 20, ∫ u : ℝ in Set.Ioo (((680 : ℝ) + (j : ℝ)) / 1600) (((680 : ℝ) + (j :
        ℝ) + 1) / 1600),
        u ^ m * hpRiemannThetaDifferentialKernel u) =
      ∫ u : ℝ in Set.Ioo (34 / 80 : ℝ) ((34 + 1) / 80 : ℝ), u ^ m *
        hpRiemannThetaDifferentialKernel u := by
    have h := hpThetaJensen_batchCellIntegral_sum m hm 34
    have hc : ∀ j : ℕ,
        Set.Ioo (((680 : ℝ) + (j : ℝ)) / 1600) (((680 : ℝ) + (j : ℝ) + 1) / 1600) =
          Set.Ioo ((34 : ℝ) / 80 + (j : ℝ) / 1600)
            ((34 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600) := by
      intro j
      have hl : (((680 : ℝ) + (j : ℝ)) / 1600) = (34 : ℝ) / 80 + (j : ℝ) / 1600 := by ring
      have hr : (((680 : ℝ) + (j : ℝ) + 1) / 1600) = (34 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600 :=
        by
        push_cast
        ring
      rw [hl, hr]
    simp_rw [hc]
    exact h
  have h0 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((680 : ℝ) + (j : ℝ)) / 1600) (((680 : ℝ) + (j : ℝ) + 1) / 1600), u ^ 0
        * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((680 : ℝ) + (j : ℝ) + 1) / 1600) ^ 0 *
        hpThetaJensenCellsBatch034Upper j * ((((680 : ℝ) + (j : ℝ) + 1) / 1600) - (((680 : ℝ) + (j
        : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch034_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 0
      (Or.inl rfl)).2
  have h2 : (∑ j ∈ Finset.range 20, (((680 : ℝ) + (j : ℝ)) / 1600) ^ 2 *
    hpThetaJensenCellsBatch034Lower j * ((((680 : ℝ) + (j : ℝ) + 1) / 1600) - (((680 : ℝ) + (j :
    ℝ)) / 1600))) ≤
      ∑ j ∈ Finset.range 20,
        ∫ u : ℝ in Set.Ioo (((680 : ℝ) + (j : ℝ)) / 1600) (((680 : ℝ) + (j : ℝ) + 1) / 1600), u ^
          2 * hpRiemannThetaDifferentialKernel u := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch034_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 2
      (Or.inr (Or.inl rfl))).1
  have h4 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((680 : ℝ) + (j : ℝ)) / 1600) (((680 : ℝ) + (j : ℝ) + 1) / 1600), u ^ 4
        * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((680 : ℝ) + (j : ℝ) + 1) / 1600) ^ 4 *
        hpThetaJensenCellsBatch034Upper j * ((((680 : ℝ) + (j : ℝ) + 1) / 1600) - (((680 : ℝ) + (j
        : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch034_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 4
      (Or.inr (Or.inr rfl))).2
  rw [hs 0 (Or.inl rfl)] at h0
  rw [hs 2 (Or.inr (Or.inl rfl))] at h2
  rw [hs 4 (Or.inr (Or.inr rfl))] at h4
  norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch034Lower,
    hpThetaJensenCellsBatch034Upper] at h0 h2 h4
  norm_num [hpThetaJensenBatchZeroUpper, hpThetaJensenBatchSecondLower,
    hpThetaJensenBatchFourthUpper]
  exact ⟨le_trans h0 (by norm_num), le_trans (by norm_num) h2,
    le_trans h4 (by norm_num)⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Twenty rational terms are verified for each of the three moment orders.
theorem hpThetaJensenCellsBatch035_finiteIntegral_bounds :
    (∫ u : ℝ in Set.Ioo (35 / 80 : ℝ) ((35 + 1) / 80 : ℝ), u ^ 0 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchZeroUpper 35 ∧
    hpThetaJensenBatchSecondLower 35 ≤
        (∫ u : ℝ in Set.Ioo (35 / 80 : ℝ) ((35 + 1) / 80 : ℝ), u ^ 2 *
          hpRiemannThetaDifferentialKernel u) ∧
    (∫ u : ℝ in Set.Ioo (35 / 80 : ℝ) ((35 + 1) / 80 : ℝ), u ^ 4 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchFourthUpper 35 := by
  have hs (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
      (∑ j ∈ Finset.range 20, ∫ u : ℝ in Set.Ioo (((700 : ℝ) + (j : ℝ)) / 1600) (((700 : ℝ) + (j :
        ℝ) + 1) / 1600),
        u ^ m * hpRiemannThetaDifferentialKernel u) =
      ∫ u : ℝ in Set.Ioo (35 / 80 : ℝ) ((35 + 1) / 80 : ℝ), u ^ m *
        hpRiemannThetaDifferentialKernel u := by
    have h := hpThetaJensen_batchCellIntegral_sum m hm 35
    have hc : ∀ j : ℕ,
        Set.Ioo (((700 : ℝ) + (j : ℝ)) / 1600) (((700 : ℝ) + (j : ℝ) + 1) / 1600) =
          Set.Ioo ((35 : ℝ) / 80 + (j : ℝ) / 1600)
            ((35 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600) := by
      intro j
      have hl : (((700 : ℝ) + (j : ℝ)) / 1600) = (35 : ℝ) / 80 + (j : ℝ) / 1600 := by ring
      have hr : (((700 : ℝ) + (j : ℝ) + 1) / 1600) = (35 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600 :=
        by
        push_cast
        ring
      rw [hl, hr]
    simp_rw [hc]
    exact h
  have h0 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((700 : ℝ) + (j : ℝ)) / 1600) (((700 : ℝ) + (j : ℝ) + 1) / 1600), u ^ 0
        * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((700 : ℝ) + (j : ℝ) + 1) / 1600) ^ 0 *
        hpThetaJensenCellsBatch035Upper j * ((((700 : ℝ) + (j : ℝ) + 1) / 1600) - (((700 : ℝ) + (j
        : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch035_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 0
      (Or.inl rfl)).2
  have h2 : (∑ j ∈ Finset.range 20, (((700 : ℝ) + (j : ℝ)) / 1600) ^ 2 *
    hpThetaJensenCellsBatch035Lower j * ((((700 : ℝ) + (j : ℝ) + 1) / 1600) - (((700 : ℝ) + (j :
    ℝ)) / 1600))) ≤
      ∑ j ∈ Finset.range 20,
        ∫ u : ℝ in Set.Ioo (((700 : ℝ) + (j : ℝ)) / 1600) (((700 : ℝ) + (j : ℝ) + 1) / 1600), u ^
          2 * hpRiemannThetaDifferentialKernel u := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch035_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 2
      (Or.inr (Or.inl rfl))).1
  have h4 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((700 : ℝ) + (j : ℝ)) / 1600) (((700 : ℝ) + (j : ℝ) + 1) / 1600), u ^ 4
        * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((700 : ℝ) + (j : ℝ) + 1) / 1600) ^ 4 *
        hpThetaJensenCellsBatch035Upper j * ((((700 : ℝ) + (j : ℝ) + 1) / 1600) - (((700 : ℝ) + (j
        : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch035_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 4
      (Or.inr (Or.inr rfl))).2
  rw [hs 0 (Or.inl rfl)] at h0
  rw [hs 2 (Or.inr (Or.inl rfl))] at h2
  rw [hs 4 (Or.inr (Or.inr rfl))] at h4
  norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch035Lower,
    hpThetaJensenCellsBatch035Upper] at h0 h2 h4
  norm_num [hpThetaJensenBatchZeroUpper, hpThetaJensenBatchSecondLower,
    hpThetaJensenBatchFourthUpper]
  exact ⟨le_trans h0 (by norm_num), le_trans (by norm_num) h2,
    le_trans h4 (by norm_num)⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Twenty rational terms are verified for each of the three moment orders.
theorem hpThetaJensenCellsBatch036_finiteIntegral_bounds :
    (∫ u : ℝ in Set.Ioo (36 / 80 : ℝ) ((36 + 1) / 80 : ℝ), u ^ 0 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchZeroUpper 36 ∧
    hpThetaJensenBatchSecondLower 36 ≤
        (∫ u : ℝ in Set.Ioo (36 / 80 : ℝ) ((36 + 1) / 80 : ℝ), u ^ 2 *
          hpRiemannThetaDifferentialKernel u) ∧
    (∫ u : ℝ in Set.Ioo (36 / 80 : ℝ) ((36 + 1) / 80 : ℝ), u ^ 4 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchFourthUpper 36 := by
  have hs (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
      (∑ j ∈ Finset.range 20, ∫ u : ℝ in Set.Ioo (((720 : ℝ) + (j : ℝ)) / 1600) (((720 : ℝ) + (j :
        ℝ) + 1) / 1600),
        u ^ m * hpRiemannThetaDifferentialKernel u) =
      ∫ u : ℝ in Set.Ioo (36 / 80 : ℝ) ((36 + 1) / 80 : ℝ), u ^ m *
        hpRiemannThetaDifferentialKernel u := by
    have h := hpThetaJensen_batchCellIntegral_sum m hm 36
    have hc : ∀ j : ℕ,
        Set.Ioo (((720 : ℝ) + (j : ℝ)) / 1600) (((720 : ℝ) + (j : ℝ) + 1) / 1600) =
          Set.Ioo ((36 : ℝ) / 80 + (j : ℝ) / 1600)
            ((36 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600) := by
      intro j
      have hl : (((720 : ℝ) + (j : ℝ)) / 1600) = (36 : ℝ) / 80 + (j : ℝ) / 1600 := by ring
      have hr : (((720 : ℝ) + (j : ℝ) + 1) / 1600) = (36 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600 :=
        by
        push_cast
        ring
      rw [hl, hr]
    simp_rw [hc]
    exact h
  have h0 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((720 : ℝ) + (j : ℝ)) / 1600) (((720 : ℝ) + (j : ℝ) + 1) / 1600), u ^ 0
        * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((720 : ℝ) + (j : ℝ) + 1) / 1600) ^ 0 *
        hpThetaJensenCellsBatch036Upper j * ((((720 : ℝ) + (j : ℝ) + 1) / 1600) - (((720 : ℝ) + (j
        : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch036_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 0
      (Or.inl rfl)).2
  have h2 : (∑ j ∈ Finset.range 20, (((720 : ℝ) + (j : ℝ)) / 1600) ^ 2 *
    hpThetaJensenCellsBatch036Lower j * ((((720 : ℝ) + (j : ℝ) + 1) / 1600) - (((720 : ℝ) + (j :
    ℝ)) / 1600))) ≤
      ∑ j ∈ Finset.range 20,
        ∫ u : ℝ in Set.Ioo (((720 : ℝ) + (j : ℝ)) / 1600) (((720 : ℝ) + (j : ℝ) + 1) / 1600), u ^
          2 * hpRiemannThetaDifferentialKernel u := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch036_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 2
      (Or.inr (Or.inl rfl))).1
  have h4 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((720 : ℝ) + (j : ℝ)) / 1600) (((720 : ℝ) + (j : ℝ) + 1) / 1600), u ^ 4
        * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((720 : ℝ) + (j : ℝ) + 1) / 1600) ^ 4 *
        hpThetaJensenCellsBatch036Upper j * ((((720 : ℝ) + (j : ℝ) + 1) / 1600) - (((720 : ℝ) + (j
        : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch036_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 4
      (Or.inr (Or.inr rfl))).2
  rw [hs 0 (Or.inl rfl)] at h0
  rw [hs 2 (Or.inr (Or.inl rfl))] at h2
  rw [hs 4 (Or.inr (Or.inr rfl))] at h4
  norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch036Lower,
    hpThetaJensenCellsBatch036Upper] at h0 h2 h4
  norm_num [hpThetaJensenBatchZeroUpper, hpThetaJensenBatchSecondLower,
    hpThetaJensenBatchFourthUpper]
  exact ⟨le_trans h0 (by norm_num), le_trans (by norm_num) h2,
    le_trans h4 (by norm_num)⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Twenty rational terms are verified for each of the three moment orders.
theorem hpThetaJensenCellsBatch037_finiteIntegral_bounds :
    (∫ u : ℝ in Set.Ioo (37 / 80 : ℝ) ((37 + 1) / 80 : ℝ), u ^ 0 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchZeroUpper 37 ∧
    hpThetaJensenBatchSecondLower 37 ≤
        (∫ u : ℝ in Set.Ioo (37 / 80 : ℝ) ((37 + 1) / 80 : ℝ), u ^ 2 *
          hpRiemannThetaDifferentialKernel u) ∧
    (∫ u : ℝ in Set.Ioo (37 / 80 : ℝ) ((37 + 1) / 80 : ℝ), u ^ 4 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchFourthUpper 37 := by
  have hs (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
      (∑ j ∈ Finset.range 20, ∫ u : ℝ in Set.Ioo (((740 : ℝ) + (j : ℝ)) / 1600) (((740 : ℝ) + (j :
        ℝ) + 1) / 1600),
        u ^ m * hpRiemannThetaDifferentialKernel u) =
      ∫ u : ℝ in Set.Ioo (37 / 80 : ℝ) ((37 + 1) / 80 : ℝ), u ^ m *
        hpRiemannThetaDifferentialKernel u := by
    have h := hpThetaJensen_batchCellIntegral_sum m hm 37
    have hc : ∀ j : ℕ,
        Set.Ioo (((740 : ℝ) + (j : ℝ)) / 1600) (((740 : ℝ) + (j : ℝ) + 1) / 1600) =
          Set.Ioo ((37 : ℝ) / 80 + (j : ℝ) / 1600)
            ((37 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600) := by
      intro j
      have hl : (((740 : ℝ) + (j : ℝ)) / 1600) = (37 : ℝ) / 80 + (j : ℝ) / 1600 := by ring
      have hr : (((740 : ℝ) + (j : ℝ) + 1) / 1600) = (37 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600 :=
        by
        push_cast
        ring
      rw [hl, hr]
    simp_rw [hc]
    exact h
  have h0 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((740 : ℝ) + (j : ℝ)) / 1600) (((740 : ℝ) + (j : ℝ) + 1) / 1600), u ^ 0
        * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((740 : ℝ) + (j : ℝ) + 1) / 1600) ^ 0 *
        hpThetaJensenCellsBatch037Upper j * ((((740 : ℝ) + (j : ℝ) + 1) / 1600) - (((740 : ℝ) + (j
        : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch037_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 0
      (Or.inl rfl)).2
  have h2 : (∑ j ∈ Finset.range 20, (((740 : ℝ) + (j : ℝ)) / 1600) ^ 2 *
    hpThetaJensenCellsBatch037Lower j * ((((740 : ℝ) + (j : ℝ) + 1) / 1600) - (((740 : ℝ) + (j :
    ℝ)) / 1600))) ≤
      ∑ j ∈ Finset.range 20,
        ∫ u : ℝ in Set.Ioo (((740 : ℝ) + (j : ℝ)) / 1600) (((740 : ℝ) + (j : ℝ) + 1) / 1600), u ^
          2 * hpRiemannThetaDifferentialKernel u := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch037_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 2
      (Or.inr (Or.inl rfl))).1
  have h4 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((740 : ℝ) + (j : ℝ)) / 1600) (((740 : ℝ) + (j : ℝ) + 1) / 1600), u ^ 4
        * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((740 : ℝ) + (j : ℝ) + 1) / 1600) ^ 4 *
        hpThetaJensenCellsBatch037Upper j * ((((740 : ℝ) + (j : ℝ) + 1) / 1600) - (((740 : ℝ) + (j
        : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch037_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 4
      (Or.inr (Or.inr rfl))).2
  rw [hs 0 (Or.inl rfl)] at h0
  rw [hs 2 (Or.inr (Or.inl rfl))] at h2
  rw [hs 4 (Or.inr (Or.inr rfl))] at h4
  norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch037Lower,
    hpThetaJensenCellsBatch037Upper] at h0 h2 h4
  norm_num [hpThetaJensenBatchZeroUpper, hpThetaJensenBatchSecondLower,
    hpThetaJensenBatchFourthUpper]
  exact ⟨le_trans h0 (by norm_num), le_trans (by norm_num) h2,
    le_trans h4 (by norm_num)⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Twenty rational terms are verified for each of the three moment orders.
theorem hpThetaJensenCellsBatch038_finiteIntegral_bounds :
    (∫ u : ℝ in Set.Ioo (38 / 80 : ℝ) ((38 + 1) / 80 : ℝ), u ^ 0 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchZeroUpper 38 ∧
    hpThetaJensenBatchSecondLower 38 ≤
        (∫ u : ℝ in Set.Ioo (38 / 80 : ℝ) ((38 + 1) / 80 : ℝ), u ^ 2 *
          hpRiemannThetaDifferentialKernel u) ∧
    (∫ u : ℝ in Set.Ioo (38 / 80 : ℝ) ((38 + 1) / 80 : ℝ), u ^ 4 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchFourthUpper 38 := by
  have hs (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
      (∑ j ∈ Finset.range 20, ∫ u : ℝ in Set.Ioo (((760 : ℝ) + (j : ℝ)) / 1600) (((760 : ℝ) + (j :
        ℝ) + 1) / 1600),
        u ^ m * hpRiemannThetaDifferentialKernel u) =
      ∫ u : ℝ in Set.Ioo (38 / 80 : ℝ) ((38 + 1) / 80 : ℝ), u ^ m *
        hpRiemannThetaDifferentialKernel u := by
    have h := hpThetaJensen_batchCellIntegral_sum m hm 38
    have hc : ∀ j : ℕ,
        Set.Ioo (((760 : ℝ) + (j : ℝ)) / 1600) (((760 : ℝ) + (j : ℝ) + 1) / 1600) =
          Set.Ioo ((38 : ℝ) / 80 + (j : ℝ) / 1600)
            ((38 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600) := by
      intro j
      have hl : (((760 : ℝ) + (j : ℝ)) / 1600) = (38 : ℝ) / 80 + (j : ℝ) / 1600 := by ring
      have hr : (((760 : ℝ) + (j : ℝ) + 1) / 1600) = (38 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600 :=
        by
        push_cast
        ring
      rw [hl, hr]
    simp_rw [hc]
    exact h
  have h0 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((760 : ℝ) + (j : ℝ)) / 1600) (((760 : ℝ) + (j : ℝ) + 1) / 1600), u ^ 0
        * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((760 : ℝ) + (j : ℝ) + 1) / 1600) ^ 0 *
        hpThetaJensenCellsBatch038Upper j * ((((760 : ℝ) + (j : ℝ) + 1) / 1600) - (((760 : ℝ) + (j
        : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch038_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 0
      (Or.inl rfl)).2
  have h2 : (∑ j ∈ Finset.range 20, (((760 : ℝ) + (j : ℝ)) / 1600) ^ 2 *
    hpThetaJensenCellsBatch038Lower j * ((((760 : ℝ) + (j : ℝ) + 1) / 1600) - (((760 : ℝ) + (j :
    ℝ)) / 1600))) ≤
      ∑ j ∈ Finset.range 20,
        ∫ u : ℝ in Set.Ioo (((760 : ℝ) + (j : ℝ)) / 1600) (((760 : ℝ) + (j : ℝ) + 1) / 1600), u ^
          2 * hpRiemannThetaDifferentialKernel u := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch038_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 2
      (Or.inr (Or.inl rfl))).1
  have h4 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((760 : ℝ) + (j : ℝ)) / 1600) (((760 : ℝ) + (j : ℝ) + 1) / 1600), u ^ 4
        * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((760 : ℝ) + (j : ℝ) + 1) / 1600) ^ 4 *
        hpThetaJensenCellsBatch038Upper j * ((((760 : ℝ) + (j : ℝ) + 1) / 1600) - (((760 : ℝ) + (j
        : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch038_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 4
      (Or.inr (Or.inr rfl))).2
  rw [hs 0 (Or.inl rfl)] at h0
  rw [hs 2 (Or.inr (Or.inl rfl))] at h2
  rw [hs 4 (Or.inr (Or.inr rfl))] at h4
  norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch038Lower,
    hpThetaJensenCellsBatch038Upper] at h0 h2 h4
  norm_num [hpThetaJensenBatchZeroUpper, hpThetaJensenBatchSecondLower,
    hpThetaJensenBatchFourthUpper]
  exact ⟨le_trans h0 (by norm_num), le_trans (by norm_num) h2,
    le_trans h4 (by norm_num)⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Twenty rational terms are verified for each of the three moment orders.
theorem hpThetaJensenCellsBatch039_finiteIntegral_bounds :
    (∫ u : ℝ in Set.Ioo (39 / 80 : ℝ) ((39 + 1) / 80 : ℝ), u ^ 0 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchZeroUpper 39 ∧
    hpThetaJensenBatchSecondLower 39 ≤
        (∫ u : ℝ in Set.Ioo (39 / 80 : ℝ) ((39 + 1) / 80 : ℝ), u ^ 2 *
          hpRiemannThetaDifferentialKernel u) ∧
    (∫ u : ℝ in Set.Ioo (39 / 80 : ℝ) ((39 + 1) / 80 : ℝ), u ^ 4 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchFourthUpper 39 := by
  have hs (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
      (∑ j ∈ Finset.range 20, ∫ u : ℝ in Set.Ioo (((780 : ℝ) + (j : ℝ)) / 1600) (((780 : ℝ) + (j :
        ℝ) + 1) / 1600),
        u ^ m * hpRiemannThetaDifferentialKernel u) =
      ∫ u : ℝ in Set.Ioo (39 / 80 : ℝ) ((39 + 1) / 80 : ℝ), u ^ m *
        hpRiemannThetaDifferentialKernel u := by
    have h := hpThetaJensen_batchCellIntegral_sum m hm 39
    have hc : ∀ j : ℕ,
        Set.Ioo (((780 : ℝ) + (j : ℝ)) / 1600) (((780 : ℝ) + (j : ℝ) + 1) / 1600) =
          Set.Ioo ((39 : ℝ) / 80 + (j : ℝ) / 1600)
            ((39 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600) := by
      intro j
      have hl : (((780 : ℝ) + (j : ℝ)) / 1600) = (39 : ℝ) / 80 + (j : ℝ) / 1600 := by ring
      have hr : (((780 : ℝ) + (j : ℝ) + 1) / 1600) = (39 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600 :=
        by
        push_cast
        ring
      rw [hl, hr]
    simp_rw [hc]
    exact h
  have h0 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((780 : ℝ) + (j : ℝ)) / 1600) (((780 : ℝ) + (j : ℝ) + 1) / 1600), u ^ 0
        * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((780 : ℝ) + (j : ℝ) + 1) / 1600) ^ 0 *
        hpThetaJensenCellsBatch039Upper j * ((((780 : ℝ) + (j : ℝ) + 1) / 1600) - (((780 : ℝ) + (j
        : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch039_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 0
      (Or.inl rfl)).2
  have h2 : (∑ j ∈ Finset.range 20, (((780 : ℝ) + (j : ℝ)) / 1600) ^ 2 *
    hpThetaJensenCellsBatch039Lower j * ((((780 : ℝ) + (j : ℝ) + 1) / 1600) - (((780 : ℝ) + (j :
    ℝ)) / 1600))) ≤
      ∑ j ∈ Finset.range 20,
        ∫ u : ℝ in Set.Ioo (((780 : ℝ) + (j : ℝ)) / 1600) (((780 : ℝ) + (j : ℝ) + 1) / 1600), u ^
          2 * hpRiemannThetaDifferentialKernel u := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch039_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 2
      (Or.inr (Or.inl rfl))).1
  have h4 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((780 : ℝ) + (j : ℝ)) / 1600) (((780 : ℝ) + (j : ℝ) + 1) / 1600), u ^ 4
        * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((780 : ℝ) + (j : ℝ) + 1) / 1600) ^ 4 *
        hpThetaJensenCellsBatch039Upper j * ((((780 : ℝ) + (j : ℝ) + 1) / 1600) - (((780 : ℝ) + (j
        : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch039_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 4
      (Or.inr (Or.inr rfl))).2
  rw [hs 0 (Or.inl rfl)] at h0
  rw [hs 2 (Or.inr (Or.inl rfl))] at h2
  rw [hs 4 (Or.inr (Or.inr rfl))] at h4
  norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch039Lower,
    hpThetaJensenCellsBatch039Upper] at h0 h2 h4
  norm_num [hpThetaJensenBatchZeroUpper, hpThetaJensenBatchSecondLower,
    hpThetaJensenBatchFourthUpper]
  exact ⟨le_trans h0 (by norm_num), le_trans (by norm_num) h2,
    le_trans h4 (by norm_num)⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Twenty rational terms are verified for each of the three moment orders.
theorem hpThetaJensenCellsBatch040_finiteIntegral_bounds :
    (∫ u : ℝ in Set.Ioo (40 / 80 : ℝ) ((40 + 1) / 80 : ℝ), u ^ 0 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchZeroUpper 40 ∧
    hpThetaJensenBatchSecondLower 40 ≤
        (∫ u : ℝ in Set.Ioo (40 / 80 : ℝ) ((40 + 1) / 80 : ℝ), u ^ 2 *
          hpRiemannThetaDifferentialKernel u) ∧
    (∫ u : ℝ in Set.Ioo (40 / 80 : ℝ) ((40 + 1) / 80 : ℝ), u ^ 4 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchFourthUpper 40 := by
  have hs (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
      (∑ j ∈ Finset.range 20, ∫ u : ℝ in Set.Ioo (((800 : ℝ) + (j : ℝ)) / 1600) (((800 : ℝ) + (j :
        ℝ) + 1) / 1600),
        u ^ m * hpRiemannThetaDifferentialKernel u) =
      ∫ u : ℝ in Set.Ioo (40 / 80 : ℝ) ((40 + 1) / 80 : ℝ), u ^ m *
        hpRiemannThetaDifferentialKernel u := by
    have h := hpThetaJensen_batchCellIntegral_sum m hm 40
    have hc : ∀ j : ℕ,
        Set.Ioo (((800 : ℝ) + (j : ℝ)) / 1600) (((800 : ℝ) + (j : ℝ) + 1) / 1600) =
          Set.Ioo ((40 : ℝ) / 80 + (j : ℝ) / 1600)
            ((40 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600) := by
      intro j
      have hl : (((800 : ℝ) + (j : ℝ)) / 1600) = (40 : ℝ) / 80 + (j : ℝ) / 1600 := by ring
      have hr : (((800 : ℝ) + (j : ℝ) + 1) / 1600) = (40 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600 :=
        by
        push_cast
        ring
      rw [hl, hr]
    simp_rw [hc]
    exact h
  have h0 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((800 : ℝ) + (j : ℝ)) / 1600) (((800 : ℝ) + (j : ℝ) + 1) / 1600), u ^ 0
        * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((800 : ℝ) + (j : ℝ) + 1) / 1600) ^ 0 *
        hpThetaJensenCellsBatch040Upper j * ((((800 : ℝ) + (j : ℝ) + 1) / 1600) - (((800 : ℝ) + (j
        : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch040_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 0
      (Or.inl rfl)).2
  have h2 : (∑ j ∈ Finset.range 20, (((800 : ℝ) + (j : ℝ)) / 1600) ^ 2 *
    hpThetaJensenCellsBatch040Lower j * ((((800 : ℝ) + (j : ℝ) + 1) / 1600) - (((800 : ℝ) + (j :
    ℝ)) / 1600))) ≤
      ∑ j ∈ Finset.range 20,
        ∫ u : ℝ in Set.Ioo (((800 : ℝ) + (j : ℝ)) / 1600) (((800 : ℝ) + (j : ℝ) + 1) / 1600), u ^
          2 * hpRiemannThetaDifferentialKernel u := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch040_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 2
      (Or.inr (Or.inl rfl))).1
  have h4 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((800 : ℝ) + (j : ℝ)) / 1600) (((800 : ℝ) + (j : ℝ) + 1) / 1600), u ^ 4
        * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((800 : ℝ) + (j : ℝ) + 1) / 1600) ^ 4 *
        hpThetaJensenCellsBatch040Upper j * ((((800 : ℝ) + (j : ℝ) + 1) / 1600) - (((800 : ℝ) + (j
        : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch040_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 4
      (Or.inr (Or.inr rfl))).2
  rw [hs 0 (Or.inl rfl)] at h0
  rw [hs 2 (Or.inr (Or.inl rfl))] at h2
  rw [hs 4 (Or.inr (Or.inr rfl))] at h4
  norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch040Lower,
    hpThetaJensenCellsBatch040Upper] at h0 h2 h4
  norm_num [hpThetaJensenBatchZeroUpper, hpThetaJensenBatchSecondLower,
    hpThetaJensenBatchFourthUpper]
  exact ⟨le_trans h0 (by norm_num), le_trans (by norm_num) h2,
    le_trans h4 (by norm_num)⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Twenty rational terms are verified for each of the three moment orders.
theorem hpThetaJensenCellsBatch041_finiteIntegral_bounds :
    (∫ u : ℝ in Set.Ioo (41 / 80 : ℝ) ((41 + 1) / 80 : ℝ), u ^ 0 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchZeroUpper 41 ∧
    hpThetaJensenBatchSecondLower 41 ≤
        (∫ u : ℝ in Set.Ioo (41 / 80 : ℝ) ((41 + 1) / 80 : ℝ), u ^ 2 *
          hpRiemannThetaDifferentialKernel u) ∧
    (∫ u : ℝ in Set.Ioo (41 / 80 : ℝ) ((41 + 1) / 80 : ℝ), u ^ 4 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchFourthUpper 41 := by
  have hs (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
      (∑ j ∈ Finset.range 20, ∫ u : ℝ in Set.Ioo (((820 : ℝ) + (j : ℝ)) / 1600) (((820 : ℝ) + (j :
        ℝ) + 1) / 1600),
        u ^ m * hpRiemannThetaDifferentialKernel u) =
      ∫ u : ℝ in Set.Ioo (41 / 80 : ℝ) ((41 + 1) / 80 : ℝ), u ^ m *
        hpRiemannThetaDifferentialKernel u := by
    have h := hpThetaJensen_batchCellIntegral_sum m hm 41
    have hc : ∀ j : ℕ,
        Set.Ioo (((820 : ℝ) + (j : ℝ)) / 1600) (((820 : ℝ) + (j : ℝ) + 1) / 1600) =
          Set.Ioo ((41 : ℝ) / 80 + (j : ℝ) / 1600)
            ((41 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600) := by
      intro j
      have hl : (((820 : ℝ) + (j : ℝ)) / 1600) = (41 : ℝ) / 80 + (j : ℝ) / 1600 := by ring
      have hr : (((820 : ℝ) + (j : ℝ) + 1) / 1600) = (41 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600 :=
        by
        push_cast
        ring
      rw [hl, hr]
    simp_rw [hc]
    exact h
  have h0 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((820 : ℝ) + (j : ℝ)) / 1600) (((820 : ℝ) + (j : ℝ) + 1) / 1600), u ^ 0
        * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((820 : ℝ) + (j : ℝ) + 1) / 1600) ^ 0 *
        hpThetaJensenCellsBatch041Upper j * ((((820 : ℝ) + (j : ℝ) + 1) / 1600) - (((820 : ℝ) + (j
        : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch041_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 0
      (Or.inl rfl)).2
  have h2 : (∑ j ∈ Finset.range 20, (((820 : ℝ) + (j : ℝ)) / 1600) ^ 2 *
    hpThetaJensenCellsBatch041Lower j * ((((820 : ℝ) + (j : ℝ) + 1) / 1600) - (((820 : ℝ) + (j :
    ℝ)) / 1600))) ≤
      ∑ j ∈ Finset.range 20,
        ∫ u : ℝ in Set.Ioo (((820 : ℝ) + (j : ℝ)) / 1600) (((820 : ℝ) + (j : ℝ) + 1) / 1600), u ^
          2 * hpRiemannThetaDifferentialKernel u := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch041_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 2
      (Or.inr (Or.inl rfl))).1
  have h4 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((820 : ℝ) + (j : ℝ)) / 1600) (((820 : ℝ) + (j : ℝ) + 1) / 1600), u ^ 4
        * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((820 : ℝ) + (j : ℝ) + 1) / 1600) ^ 4 *
        hpThetaJensenCellsBatch041Upper j * ((((820 : ℝ) + (j : ℝ) + 1) / 1600) - (((820 : ℝ) + (j
        : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch041_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 4
      (Or.inr (Or.inr rfl))).2
  rw [hs 0 (Or.inl rfl)] at h0
  rw [hs 2 (Or.inr (Or.inl rfl))] at h2
  rw [hs 4 (Or.inr (Or.inr rfl))] at h4
  norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch041Lower,
    hpThetaJensenCellsBatch041Upper] at h0 h2 h4
  norm_num [hpThetaJensenBatchZeroUpper, hpThetaJensenBatchSecondLower,
    hpThetaJensenBatchFourthUpper]
  exact ⟨le_trans h0 (by norm_num), le_trans (by norm_num) h2,
    le_trans h4 (by norm_num)⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Twenty rational terms are verified for each of the three moment orders.
theorem hpThetaJensenCellsBatch042_finiteIntegral_bounds :
    (∫ u : ℝ in Set.Ioo (42 / 80 : ℝ) ((42 + 1) / 80 : ℝ), u ^ 0 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchZeroUpper 42 ∧
    hpThetaJensenBatchSecondLower 42 ≤
        (∫ u : ℝ in Set.Ioo (42 / 80 : ℝ) ((42 + 1) / 80 : ℝ), u ^ 2 *
          hpRiemannThetaDifferentialKernel u) ∧
    (∫ u : ℝ in Set.Ioo (42 / 80 : ℝ) ((42 + 1) / 80 : ℝ), u ^ 4 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchFourthUpper 42 := by
  have hs (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
      (∑ j ∈ Finset.range 20, ∫ u : ℝ in Set.Ioo (((840 : ℝ) + (j : ℝ)) / 1600) (((840 : ℝ) + (j :
        ℝ) + 1) / 1600),
        u ^ m * hpRiemannThetaDifferentialKernel u) =
      ∫ u : ℝ in Set.Ioo (42 / 80 : ℝ) ((42 + 1) / 80 : ℝ), u ^ m *
        hpRiemannThetaDifferentialKernel u := by
    have h := hpThetaJensen_batchCellIntegral_sum m hm 42
    have hc : ∀ j : ℕ,
        Set.Ioo (((840 : ℝ) + (j : ℝ)) / 1600) (((840 : ℝ) + (j : ℝ) + 1) / 1600) =
          Set.Ioo ((42 : ℝ) / 80 + (j : ℝ) / 1600)
            ((42 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600) := by
      intro j
      have hl : (((840 : ℝ) + (j : ℝ)) / 1600) = (42 : ℝ) / 80 + (j : ℝ) / 1600 := by ring
      have hr : (((840 : ℝ) + (j : ℝ) + 1) / 1600) = (42 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600 :=
        by
        push_cast
        ring
      rw [hl, hr]
    simp_rw [hc]
    exact h
  have h0 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((840 : ℝ) + (j : ℝ)) / 1600) (((840 : ℝ) + (j : ℝ) + 1) / 1600), u ^ 0
        * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((840 : ℝ) + (j : ℝ) + 1) / 1600) ^ 0 *
        hpThetaJensenCellsBatch042Upper j * ((((840 : ℝ) + (j : ℝ) + 1) / 1600) - (((840 : ℝ) + (j
        : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch042_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 0
      (Or.inl rfl)).2
  have h2 : (∑ j ∈ Finset.range 20, (((840 : ℝ) + (j : ℝ)) / 1600) ^ 2 *
    hpThetaJensenCellsBatch042Lower j * ((((840 : ℝ) + (j : ℝ) + 1) / 1600) - (((840 : ℝ) + (j :
    ℝ)) / 1600))) ≤
      ∑ j ∈ Finset.range 20,
        ∫ u : ℝ in Set.Ioo (((840 : ℝ) + (j : ℝ)) / 1600) (((840 : ℝ) + (j : ℝ) + 1) / 1600), u ^
          2 * hpRiemannThetaDifferentialKernel u := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch042_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 2
      (Or.inr (Or.inl rfl))).1
  have h4 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((840 : ℝ) + (j : ℝ)) / 1600) (((840 : ℝ) + (j : ℝ) + 1) / 1600), u ^ 4
        * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((840 : ℝ) + (j : ℝ) + 1) / 1600) ^ 4 *
        hpThetaJensenCellsBatch042Upper j * ((((840 : ℝ) + (j : ℝ) + 1) / 1600) - (((840 : ℝ) + (j
        : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch042_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 4
      (Or.inr (Or.inr rfl))).2
  rw [hs 0 (Or.inl rfl)] at h0
  rw [hs 2 (Or.inr (Or.inl rfl))] at h2
  rw [hs 4 (Or.inr (Or.inr rfl))] at h4
  norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch042Lower,
    hpThetaJensenCellsBatch042Upper] at h0 h2 h4
  norm_num [hpThetaJensenBatchZeroUpper, hpThetaJensenBatchSecondLower,
    hpThetaJensenBatchFourthUpper]
  exact ⟨le_trans h0 (by norm_num), le_trans (by norm_num) h2,
    le_trans h4 (by norm_num)⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Twenty rational terms are verified for each of the three moment orders.
theorem hpThetaJensenCellsBatch043_finiteIntegral_bounds :
    (∫ u : ℝ in Set.Ioo (43 / 80 : ℝ) ((43 + 1) / 80 : ℝ), u ^ 0 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchZeroUpper 43 ∧
    hpThetaJensenBatchSecondLower 43 ≤
        (∫ u : ℝ in Set.Ioo (43 / 80 : ℝ) ((43 + 1) / 80 : ℝ), u ^ 2 *
          hpRiemannThetaDifferentialKernel u) ∧
    (∫ u : ℝ in Set.Ioo (43 / 80 : ℝ) ((43 + 1) / 80 : ℝ), u ^ 4 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchFourthUpper 43 := by
  have hs (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
      (∑ j ∈ Finset.range 20, ∫ u : ℝ in Set.Ioo (((860 : ℝ) + (j : ℝ)) / 1600) (((860 : ℝ) + (j :
        ℝ) + 1) / 1600),
        u ^ m * hpRiemannThetaDifferentialKernel u) =
      ∫ u : ℝ in Set.Ioo (43 / 80 : ℝ) ((43 + 1) / 80 : ℝ), u ^ m *
        hpRiemannThetaDifferentialKernel u := by
    have h := hpThetaJensen_batchCellIntegral_sum m hm 43
    have hc : ∀ j : ℕ,
        Set.Ioo (((860 : ℝ) + (j : ℝ)) / 1600) (((860 : ℝ) + (j : ℝ) + 1) / 1600) =
          Set.Ioo ((43 : ℝ) / 80 + (j : ℝ) / 1600)
            ((43 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600) := by
      intro j
      have hl : (((860 : ℝ) + (j : ℝ)) / 1600) = (43 : ℝ) / 80 + (j : ℝ) / 1600 := by ring
      have hr : (((860 : ℝ) + (j : ℝ) + 1) / 1600) = (43 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600 :=
        by
        push_cast
        ring
      rw [hl, hr]
    simp_rw [hc]
    exact h
  have h0 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((860 : ℝ) + (j : ℝ)) / 1600) (((860 : ℝ) + (j : ℝ) + 1) / 1600), u ^ 0
        * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((860 : ℝ) + (j : ℝ) + 1) / 1600) ^ 0 *
        hpThetaJensenCellsBatch043Upper j * ((((860 : ℝ) + (j : ℝ) + 1) / 1600) - (((860 : ℝ) + (j
        : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch043_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 0
      (Or.inl rfl)).2
  have h2 : (∑ j ∈ Finset.range 20, (((860 : ℝ) + (j : ℝ)) / 1600) ^ 2 *
    hpThetaJensenCellsBatch043Lower j * ((((860 : ℝ) + (j : ℝ) + 1) / 1600) - (((860 : ℝ) + (j :
    ℝ)) / 1600))) ≤
      ∑ j ∈ Finset.range 20,
        ∫ u : ℝ in Set.Ioo (((860 : ℝ) + (j : ℝ)) / 1600) (((860 : ℝ) + (j : ℝ) + 1) / 1600), u ^
          2 * hpRiemannThetaDifferentialKernel u := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch043_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 2
      (Or.inr (Or.inl rfl))).1
  have h4 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((860 : ℝ) + (j : ℝ)) / 1600) (((860 : ℝ) + (j : ℝ) + 1) / 1600), u ^ 4
        * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((860 : ℝ) + (j : ℝ) + 1) / 1600) ^ 4 *
        hpThetaJensenCellsBatch043Upper j * ((((860 : ℝ) + (j : ℝ) + 1) / 1600) - (((860 : ℝ) + (j
        : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch043_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 4
      (Or.inr (Or.inr rfl))).2
  rw [hs 0 (Or.inl rfl)] at h0
  rw [hs 2 (Or.inr (Or.inl rfl))] at h2
  rw [hs 4 (Or.inr (Or.inr rfl))] at h4
  norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch043Lower,
    hpThetaJensenCellsBatch043Upper] at h0 h2 h4
  norm_num [hpThetaJensenBatchZeroUpper, hpThetaJensenBatchSecondLower,
    hpThetaJensenBatchFourthUpper]
  exact ⟨le_trans h0 (by norm_num), le_trans (by norm_num) h2,
    le_trans h4 (by norm_num)⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Twenty rational terms are verified for each of the three moment orders.
theorem hpThetaJensenCellsBatch044_finiteIntegral_bounds :
    (∫ u : ℝ in Set.Ioo (44 / 80 : ℝ) ((44 + 1) / 80 : ℝ), u ^ 0 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchZeroUpper 44 ∧
    hpThetaJensenBatchSecondLower 44 ≤
        (∫ u : ℝ in Set.Ioo (44 / 80 : ℝ) ((44 + 1) / 80 : ℝ), u ^ 2 *
          hpRiemannThetaDifferentialKernel u) ∧
    (∫ u : ℝ in Set.Ioo (44 / 80 : ℝ) ((44 + 1) / 80 : ℝ), u ^ 4 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchFourthUpper 44 := by
  have hs (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
      (∑ j ∈ Finset.range 20, ∫ u : ℝ in Set.Ioo (((880 : ℝ) + (j : ℝ)) / 1600) (((880 : ℝ) + (j :
        ℝ) + 1) / 1600),
        u ^ m * hpRiemannThetaDifferentialKernel u) =
      ∫ u : ℝ in Set.Ioo (44 / 80 : ℝ) ((44 + 1) / 80 : ℝ), u ^ m *
        hpRiemannThetaDifferentialKernel u := by
    have h := hpThetaJensen_batchCellIntegral_sum m hm 44
    have hc : ∀ j : ℕ,
        Set.Ioo (((880 : ℝ) + (j : ℝ)) / 1600) (((880 : ℝ) + (j : ℝ) + 1) / 1600) =
          Set.Ioo ((44 : ℝ) / 80 + (j : ℝ) / 1600)
            ((44 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600) := by
      intro j
      have hl : (((880 : ℝ) + (j : ℝ)) / 1600) = (44 : ℝ) / 80 + (j : ℝ) / 1600 := by ring
      have hr : (((880 : ℝ) + (j : ℝ) + 1) / 1600) = (44 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600 :=
        by
        push_cast
        ring
      rw [hl, hr]
    simp_rw [hc]
    exact h
  have h0 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((880 : ℝ) + (j : ℝ)) / 1600) (((880 : ℝ) + (j : ℝ) + 1) / 1600), u ^ 0
        * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((880 : ℝ) + (j : ℝ) + 1) / 1600) ^ 0 *
        hpThetaJensenCellsBatch044Upper j * ((((880 : ℝ) + (j : ℝ) + 1) / 1600) - (((880 : ℝ) + (j
        : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch044_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 0
      (Or.inl rfl)).2
  have h2 : (∑ j ∈ Finset.range 20, (((880 : ℝ) + (j : ℝ)) / 1600) ^ 2 *
    hpThetaJensenCellsBatch044Lower j * ((((880 : ℝ) + (j : ℝ) + 1) / 1600) - (((880 : ℝ) + (j :
    ℝ)) / 1600))) ≤
      ∑ j ∈ Finset.range 20,
        ∫ u : ℝ in Set.Ioo (((880 : ℝ) + (j : ℝ)) / 1600) (((880 : ℝ) + (j : ℝ) + 1) / 1600), u ^
          2 * hpRiemannThetaDifferentialKernel u := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch044_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 2
      (Or.inr (Or.inl rfl))).1
  have h4 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((880 : ℝ) + (j : ℝ)) / 1600) (((880 : ℝ) + (j : ℝ) + 1) / 1600), u ^ 4
        * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((880 : ℝ) + (j : ℝ) + 1) / 1600) ^ 4 *
        hpThetaJensenCellsBatch044Upper j * ((((880 : ℝ) + (j : ℝ) + 1) / 1600) - (((880 : ℝ) + (j
        : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch044_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 4
      (Or.inr (Or.inr rfl))).2
  rw [hs 0 (Or.inl rfl)] at h0
  rw [hs 2 (Or.inr (Or.inl rfl))] at h2
  rw [hs 4 (Or.inr (Or.inr rfl))] at h4
  norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch044Lower,
    hpThetaJensenCellsBatch044Upper] at h0 h2 h4
  norm_num [hpThetaJensenBatchZeroUpper, hpThetaJensenBatchSecondLower,
    hpThetaJensenBatchFourthUpper]
  exact ⟨le_trans h0 (by norm_num), le_trans (by norm_num) h2,
    le_trans h4 (by norm_num)⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Twenty rational terms are verified for each of the three moment orders.
theorem hpThetaJensenCellsBatch045_finiteIntegral_bounds :
    (∫ u : ℝ in Set.Ioo (45 / 80 : ℝ) ((45 + 1) / 80 : ℝ), u ^ 0 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchZeroUpper 45 ∧
    hpThetaJensenBatchSecondLower 45 ≤
        (∫ u : ℝ in Set.Ioo (45 / 80 : ℝ) ((45 + 1) / 80 : ℝ), u ^ 2 *
          hpRiemannThetaDifferentialKernel u) ∧
    (∫ u : ℝ in Set.Ioo (45 / 80 : ℝ) ((45 + 1) / 80 : ℝ), u ^ 4 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchFourthUpper 45 := by
  have hs (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
      (∑ j ∈ Finset.range 20, ∫ u : ℝ in Set.Ioo (((900 : ℝ) + (j : ℝ)) / 1600) (((900 : ℝ) + (j :
        ℝ) + 1) / 1600),
        u ^ m * hpRiemannThetaDifferentialKernel u) =
      ∫ u : ℝ in Set.Ioo (45 / 80 : ℝ) ((45 + 1) / 80 : ℝ), u ^ m *
        hpRiemannThetaDifferentialKernel u := by
    have h := hpThetaJensen_batchCellIntegral_sum m hm 45
    have hc : ∀ j : ℕ,
        Set.Ioo (((900 : ℝ) + (j : ℝ)) / 1600) (((900 : ℝ) + (j : ℝ) + 1) / 1600) =
          Set.Ioo ((45 : ℝ) / 80 + (j : ℝ) / 1600)
            ((45 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600) := by
      intro j
      have hl : (((900 : ℝ) + (j : ℝ)) / 1600) = (45 : ℝ) / 80 + (j : ℝ) / 1600 := by ring
      have hr : (((900 : ℝ) + (j : ℝ) + 1) / 1600) = (45 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600 :=
        by
        push_cast
        ring
      rw [hl, hr]
    simp_rw [hc]
    exact h
  have h0 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((900 : ℝ) + (j : ℝ)) / 1600) (((900 : ℝ) + (j : ℝ) + 1) / 1600), u ^ 0
        * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((900 : ℝ) + (j : ℝ) + 1) / 1600) ^ 0 *
        hpThetaJensenCellsBatch045Upper j * ((((900 : ℝ) + (j : ℝ) + 1) / 1600) - (((900 : ℝ) + (j
        : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch045_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 0
      (Or.inl rfl)).2
  have h2 : (∑ j ∈ Finset.range 20, (((900 : ℝ) + (j : ℝ)) / 1600) ^ 2 *
    hpThetaJensenCellsBatch045Lower j * ((((900 : ℝ) + (j : ℝ) + 1) / 1600) - (((900 : ℝ) + (j :
    ℝ)) / 1600))) ≤
      ∑ j ∈ Finset.range 20,
        ∫ u : ℝ in Set.Ioo (((900 : ℝ) + (j : ℝ)) / 1600) (((900 : ℝ) + (j : ℝ) + 1) / 1600), u ^
          2 * hpRiemannThetaDifferentialKernel u := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch045_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 2
      (Or.inr (Or.inl rfl))).1
  have h4 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((900 : ℝ) + (j : ℝ)) / 1600) (((900 : ℝ) + (j : ℝ) + 1) / 1600), u ^ 4
        * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((900 : ℝ) + (j : ℝ) + 1) / 1600) ^ 4 *
        hpThetaJensenCellsBatch045Upper j * ((((900 : ℝ) + (j : ℝ) + 1) / 1600) - (((900 : ℝ) + (j
        : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch045_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 4
      (Or.inr (Or.inr rfl))).2
  rw [hs 0 (Or.inl rfl)] at h0
  rw [hs 2 (Or.inr (Or.inl rfl))] at h2
  rw [hs 4 (Or.inr (Or.inr rfl))] at h4
  norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch045Lower,
    hpThetaJensenCellsBatch045Upper] at h0 h2 h4
  norm_num [hpThetaJensenBatchZeroUpper, hpThetaJensenBatchSecondLower,
    hpThetaJensenBatchFourthUpper]
  exact ⟨le_trans h0 (by norm_num), le_trans (by norm_num) h2,
    le_trans h4 (by norm_num)⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Twenty rational terms are verified for each of the three moment orders.
theorem hpThetaJensenCellsBatch046_finiteIntegral_bounds :
    (∫ u : ℝ in Set.Ioo (46 / 80 : ℝ) ((46 + 1) / 80 : ℝ), u ^ 0 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchZeroUpper 46 ∧
    hpThetaJensenBatchSecondLower 46 ≤
        (∫ u : ℝ in Set.Ioo (46 / 80 : ℝ) ((46 + 1) / 80 : ℝ), u ^ 2 *
          hpRiemannThetaDifferentialKernel u) ∧
    (∫ u : ℝ in Set.Ioo (46 / 80 : ℝ) ((46 + 1) / 80 : ℝ), u ^ 4 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchFourthUpper 46 := by
  have hs (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
      (∑ j ∈ Finset.range 20, ∫ u : ℝ in Set.Ioo (((920 : ℝ) + (j : ℝ)) / 1600) (((920 : ℝ) + (j :
        ℝ) + 1) / 1600),
        u ^ m * hpRiemannThetaDifferentialKernel u) =
      ∫ u : ℝ in Set.Ioo (46 / 80 : ℝ) ((46 + 1) / 80 : ℝ), u ^ m *
        hpRiemannThetaDifferentialKernel u := by
    have h := hpThetaJensen_batchCellIntegral_sum m hm 46
    have hc : ∀ j : ℕ,
        Set.Ioo (((920 : ℝ) + (j : ℝ)) / 1600) (((920 : ℝ) + (j : ℝ) + 1) / 1600) =
          Set.Ioo ((46 : ℝ) / 80 + (j : ℝ) / 1600)
            ((46 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600) := by
      intro j
      have hl : (((920 : ℝ) + (j : ℝ)) / 1600) = (46 : ℝ) / 80 + (j : ℝ) / 1600 := by ring
      have hr : (((920 : ℝ) + (j : ℝ) + 1) / 1600) = (46 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600 :=
        by
        push_cast
        ring
      rw [hl, hr]
    simp_rw [hc]
    exact h
  have h0 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((920 : ℝ) + (j : ℝ)) / 1600) (((920 : ℝ) + (j : ℝ) + 1) / 1600), u ^ 0
        * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((920 : ℝ) + (j : ℝ) + 1) / 1600) ^ 0 *
        hpThetaJensenCellsBatch046Upper j * ((((920 : ℝ) + (j : ℝ) + 1) / 1600) - (((920 : ℝ) + (j
        : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch046_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 0
      (Or.inl rfl)).2
  have h2 : (∑ j ∈ Finset.range 20, (((920 : ℝ) + (j : ℝ)) / 1600) ^ 2 *
    hpThetaJensenCellsBatch046Lower j * ((((920 : ℝ) + (j : ℝ) + 1) / 1600) - (((920 : ℝ) + (j :
    ℝ)) / 1600))) ≤
      ∑ j ∈ Finset.range 20,
        ∫ u : ℝ in Set.Ioo (((920 : ℝ) + (j : ℝ)) / 1600) (((920 : ℝ) + (j : ℝ) + 1) / 1600), u ^
          2 * hpRiemannThetaDifferentialKernel u := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch046_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 2
      (Or.inr (Or.inl rfl))).1
  have h4 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((920 : ℝ) + (j : ℝ)) / 1600) (((920 : ℝ) + (j : ℝ) + 1) / 1600), u ^ 4
        * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((920 : ℝ) + (j : ℝ) + 1) / 1600) ^ 4 *
        hpThetaJensenCellsBatch046Upper j * ((((920 : ℝ) + (j : ℝ) + 1) / 1600) - (((920 : ℝ) + (j
        : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch046_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 4
      (Or.inr (Or.inr rfl))).2
  rw [hs 0 (Or.inl rfl)] at h0
  rw [hs 2 (Or.inr (Or.inl rfl))] at h2
  rw [hs 4 (Or.inr (Or.inr rfl))] at h4
  norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch046Lower,
    hpThetaJensenCellsBatch046Upper] at h0 h2 h4
  norm_num [hpThetaJensenBatchZeroUpper, hpThetaJensenBatchSecondLower,
    hpThetaJensenBatchFourthUpper]
  exact ⟨le_trans h0 (by norm_num), le_trans (by norm_num) h2,
    le_trans h4 (by norm_num)⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Twenty rational terms are verified for each of the three moment orders.
theorem hpThetaJensenCellsBatch047_finiteIntegral_bounds :
    (∫ u : ℝ in Set.Ioo (47 / 80 : ℝ) ((47 + 1) / 80 : ℝ), u ^ 0 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchZeroUpper 47 ∧
    hpThetaJensenBatchSecondLower 47 ≤
        (∫ u : ℝ in Set.Ioo (47 / 80 : ℝ) ((47 + 1) / 80 : ℝ), u ^ 2 *
          hpRiemannThetaDifferentialKernel u) ∧
    (∫ u : ℝ in Set.Ioo (47 / 80 : ℝ) ((47 + 1) / 80 : ℝ), u ^ 4 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchFourthUpper 47 := by
  have hs (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
      (∑ j ∈ Finset.range 20, ∫ u : ℝ in Set.Ioo (((940 : ℝ) + (j : ℝ)) / 1600) (((940 : ℝ) + (j :
        ℝ) + 1) / 1600),
        u ^ m * hpRiemannThetaDifferentialKernel u) =
      ∫ u : ℝ in Set.Ioo (47 / 80 : ℝ) ((47 + 1) / 80 : ℝ), u ^ m *
        hpRiemannThetaDifferentialKernel u := by
    have h := hpThetaJensen_batchCellIntegral_sum m hm 47
    have hc : ∀ j : ℕ,
        Set.Ioo (((940 : ℝ) + (j : ℝ)) / 1600) (((940 : ℝ) + (j : ℝ) + 1) / 1600) =
          Set.Ioo ((47 : ℝ) / 80 + (j : ℝ) / 1600)
            ((47 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600) := by
      intro j
      have hl : (((940 : ℝ) + (j : ℝ)) / 1600) = (47 : ℝ) / 80 + (j : ℝ) / 1600 := by ring
      have hr : (((940 : ℝ) + (j : ℝ) + 1) / 1600) = (47 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600 :=
        by
        push_cast
        ring
      rw [hl, hr]
    simp_rw [hc]
    exact h
  have h0 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((940 : ℝ) + (j : ℝ)) / 1600) (((940 : ℝ) + (j : ℝ) + 1) / 1600), u ^ 0
        * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((940 : ℝ) + (j : ℝ) + 1) / 1600) ^ 0 *
        hpThetaJensenCellsBatch047Upper j * ((((940 : ℝ) + (j : ℝ) + 1) / 1600) - (((940 : ℝ) + (j
        : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch047_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 0
      (Or.inl rfl)).2
  have h2 : (∑ j ∈ Finset.range 20, (((940 : ℝ) + (j : ℝ)) / 1600) ^ 2 *
    hpThetaJensenCellsBatch047Lower j * ((((940 : ℝ) + (j : ℝ) + 1) / 1600) - (((940 : ℝ) + (j :
    ℝ)) / 1600))) ≤
      ∑ j ∈ Finset.range 20,
        ∫ u : ℝ in Set.Ioo (((940 : ℝ) + (j : ℝ)) / 1600) (((940 : ℝ) + (j : ℝ) + 1) / 1600), u ^
          2 * hpRiemannThetaDifferentialKernel u := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch047_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 2
      (Or.inr (Or.inl rfl))).1
  have h4 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((940 : ℝ) + (j : ℝ)) / 1600) (((940 : ℝ) + (j : ℝ) + 1) / 1600), u ^ 4
        * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((940 : ℝ) + (j : ℝ) + 1) / 1600) ^ 4 *
        hpThetaJensenCellsBatch047Upper j * ((((940 : ℝ) + (j : ℝ) + 1) / 1600) - (((940 : ℝ) + (j
        : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch047_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 4
      (Or.inr (Or.inr rfl))).2
  rw [hs 0 (Or.inl rfl)] at h0
  rw [hs 2 (Or.inr (Or.inl rfl))] at h2
  rw [hs 4 (Or.inr (Or.inr rfl))] at h4
  norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch047Lower,
    hpThetaJensenCellsBatch047Upper] at h0 h2 h4
  norm_num [hpThetaJensenBatchZeroUpper, hpThetaJensenBatchSecondLower,
    hpThetaJensenBatchFourthUpper]
  exact ⟨le_trans h0 (by norm_num), le_trans (by norm_num) h2,
    le_trans h4 (by norm_num)⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Twenty rational terms are verified for each of the three moment orders.
theorem hpThetaJensenCellsBatch048_finiteIntegral_bounds :
    (∫ u : ℝ in Set.Ioo (48 / 80 : ℝ) ((48 + 1) / 80 : ℝ), u ^ 0 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchZeroUpper 48 ∧
    hpThetaJensenBatchSecondLower 48 ≤
        (∫ u : ℝ in Set.Ioo (48 / 80 : ℝ) ((48 + 1) / 80 : ℝ), u ^ 2 *
          hpRiemannThetaDifferentialKernel u) ∧
    (∫ u : ℝ in Set.Ioo (48 / 80 : ℝ) ((48 + 1) / 80 : ℝ), u ^ 4 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchFourthUpper 48 := by
  have hs (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
      (∑ j ∈ Finset.range 20, ∫ u : ℝ in Set.Ioo (((960 : ℝ) + (j : ℝ)) / 1600) (((960 : ℝ) + (j :
        ℝ) + 1) / 1600),
        u ^ m * hpRiemannThetaDifferentialKernel u) =
      ∫ u : ℝ in Set.Ioo (48 / 80 : ℝ) ((48 + 1) / 80 : ℝ), u ^ m *
        hpRiemannThetaDifferentialKernel u := by
    have h := hpThetaJensen_batchCellIntegral_sum m hm 48
    have hc : ∀ j : ℕ,
        Set.Ioo (((960 : ℝ) + (j : ℝ)) / 1600) (((960 : ℝ) + (j : ℝ) + 1) / 1600) =
          Set.Ioo ((48 : ℝ) / 80 + (j : ℝ) / 1600)
            ((48 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600) := by
      intro j
      have hl : (((960 : ℝ) + (j : ℝ)) / 1600) = (48 : ℝ) / 80 + (j : ℝ) / 1600 := by ring
      have hr : (((960 : ℝ) + (j : ℝ) + 1) / 1600) = (48 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600 :=
        by
        push_cast
        ring
      rw [hl, hr]
    simp_rw [hc]
    exact h
  have h0 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((960 : ℝ) + (j : ℝ)) / 1600) (((960 : ℝ) + (j : ℝ) + 1) / 1600), u ^ 0
        * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((960 : ℝ) + (j : ℝ) + 1) / 1600) ^ 0 *
        hpThetaJensenCellsBatch048Upper j * ((((960 : ℝ) + (j : ℝ) + 1) / 1600) - (((960 : ℝ) + (j
        : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch048_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 0
      (Or.inl rfl)).2
  have h2 : (∑ j ∈ Finset.range 20, (((960 : ℝ) + (j : ℝ)) / 1600) ^ 2 *
    hpThetaJensenCellsBatch048Lower j * ((((960 : ℝ) + (j : ℝ) + 1) / 1600) - (((960 : ℝ) + (j :
    ℝ)) / 1600))) ≤
      ∑ j ∈ Finset.range 20,
        ∫ u : ℝ in Set.Ioo (((960 : ℝ) + (j : ℝ)) / 1600) (((960 : ℝ) + (j : ℝ) + 1) / 1600), u ^
          2 * hpRiemannThetaDifferentialKernel u := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch048_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 2
      (Or.inr (Or.inl rfl))).1
  have h4 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((960 : ℝ) + (j : ℝ)) / 1600) (((960 : ℝ) + (j : ℝ) + 1) / 1600), u ^ 4
        * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((960 : ℝ) + (j : ℝ) + 1) / 1600) ^ 4 *
        hpThetaJensenCellsBatch048Upper j * ((((960 : ℝ) + (j : ℝ) + 1) / 1600) - (((960 : ℝ) + (j
        : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch048_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 4
      (Or.inr (Or.inr rfl))).2
  rw [hs 0 (Or.inl rfl)] at h0
  rw [hs 2 (Or.inr (Or.inl rfl))] at h2
  rw [hs 4 (Or.inr (Or.inr rfl))] at h4
  norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch048Lower,
    hpThetaJensenCellsBatch048Upper] at h0 h2 h4
  norm_num [hpThetaJensenBatchZeroUpper, hpThetaJensenBatchSecondLower,
    hpThetaJensenBatchFourthUpper]
  exact ⟨le_trans h0 (by norm_num), le_trans (by norm_num) h2,
    le_trans h4 (by norm_num)⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Twenty rational terms are verified for each of the three moment orders.
theorem hpThetaJensenCellsBatch049_finiteIntegral_bounds :
    (∫ u : ℝ in Set.Ioo (49 / 80 : ℝ) ((49 + 1) / 80 : ℝ), u ^ 0 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchZeroUpper 49 ∧
    hpThetaJensenBatchSecondLower 49 ≤
        (∫ u : ℝ in Set.Ioo (49 / 80 : ℝ) ((49 + 1) / 80 : ℝ), u ^ 2 *
          hpRiemannThetaDifferentialKernel u) ∧
    (∫ u : ℝ in Set.Ioo (49 / 80 : ℝ) ((49 + 1) / 80 : ℝ), u ^ 4 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchFourthUpper 49 := by
  have hs (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
      (∑ j ∈ Finset.range 20, ∫ u : ℝ in Set.Ioo (((980 : ℝ) + (j : ℝ)) / 1600) (((980 : ℝ) + (j :
        ℝ) + 1) / 1600),
        u ^ m * hpRiemannThetaDifferentialKernel u) =
      ∫ u : ℝ in Set.Ioo (49 / 80 : ℝ) ((49 + 1) / 80 : ℝ), u ^ m *
        hpRiemannThetaDifferentialKernel u := by
    have h := hpThetaJensen_batchCellIntegral_sum m hm 49
    have hc : ∀ j : ℕ,
        Set.Ioo (((980 : ℝ) + (j : ℝ)) / 1600) (((980 : ℝ) + (j : ℝ) + 1) / 1600) =
          Set.Ioo ((49 : ℝ) / 80 + (j : ℝ) / 1600)
            ((49 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600) := by
      intro j
      have hl : (((980 : ℝ) + (j : ℝ)) / 1600) = (49 : ℝ) / 80 + (j : ℝ) / 1600 := by ring
      have hr : (((980 : ℝ) + (j : ℝ) + 1) / 1600) = (49 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600 :=
        by
        push_cast
        ring
      rw [hl, hr]
    simp_rw [hc]
    exact h
  have h0 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((980 : ℝ) + (j : ℝ)) / 1600) (((980 : ℝ) + (j : ℝ) + 1) / 1600), u ^ 0
        * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((980 : ℝ) + (j : ℝ) + 1) / 1600) ^ 0 *
        hpThetaJensenCellsBatch049Upper j * ((((980 : ℝ) + (j : ℝ) + 1) / 1600) - (((980 : ℝ) + (j
        : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch049_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 0
      (Or.inl rfl)).2
  have h2 : (∑ j ∈ Finset.range 20, (((980 : ℝ) + (j : ℝ)) / 1600) ^ 2 *
    hpThetaJensenCellsBatch049Lower j * ((((980 : ℝ) + (j : ℝ) + 1) / 1600) - (((980 : ℝ) + (j :
    ℝ)) / 1600))) ≤
      ∑ j ∈ Finset.range 20,
        ∫ u : ℝ in Set.Ioo (((980 : ℝ) + (j : ℝ)) / 1600) (((980 : ℝ) + (j : ℝ) + 1) / 1600), u ^
          2 * hpRiemannThetaDifferentialKernel u := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch049_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 2
      (Or.inr (Or.inl rfl))).1
  have h4 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((980 : ℝ) + (j : ℝ)) / 1600) (((980 : ℝ) + (j : ℝ) + 1) / 1600), u ^ 4
        * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((980 : ℝ) + (j : ℝ) + 1) / 1600) ^ 4 *
        hpThetaJensenCellsBatch049Upper j * ((((980 : ℝ) + (j : ℝ) + 1) / 1600) - (((980 : ℝ) + (j
        : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch049_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 4
      (Or.inr (Or.inr rfl))).2
  rw [hs 0 (Or.inl rfl)] at h0
  rw [hs 2 (Or.inr (Or.inl rfl))] at h2
  rw [hs 4 (Or.inr (Or.inr rfl))] at h4
  norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch049Lower,
    hpThetaJensenCellsBatch049Upper] at h0 h2 h4
  norm_num [hpThetaJensenBatchZeroUpper, hpThetaJensenBatchSecondLower,
    hpThetaJensenBatchFourthUpper]
  exact ⟨le_trans h0 (by norm_num), le_trans (by norm_num) h2,
    le_trans h4 (by norm_num)⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Twenty rational terms are verified for each of the three moment orders.
theorem hpThetaJensenCellsBatch050_finiteIntegral_bounds :
    (∫ u : ℝ in Set.Ioo (50 / 80 : ℝ) ((50 + 1) / 80 : ℝ), u ^ 0 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchZeroUpper 50 ∧
    hpThetaJensenBatchSecondLower 50 ≤
        (∫ u : ℝ in Set.Ioo (50 / 80 : ℝ) ((50 + 1) / 80 : ℝ), u ^ 2 *
          hpRiemannThetaDifferentialKernel u) ∧
    (∫ u : ℝ in Set.Ioo (50 / 80 : ℝ) ((50 + 1) / 80 : ℝ), u ^ 4 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchFourthUpper 50 := by
  have hs (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
      (∑ j ∈ Finset.range 20, ∫ u : ℝ in Set.Ioo (((1000 : ℝ) + (j : ℝ)) / 1600) (((1000 : ℝ) + (j
        : ℝ) + 1) / 1600),
        u ^ m * hpRiemannThetaDifferentialKernel u) =
      ∫ u : ℝ in Set.Ioo (50 / 80 : ℝ) ((50 + 1) / 80 : ℝ), u ^ m *
        hpRiemannThetaDifferentialKernel u := by
    have h := hpThetaJensen_batchCellIntegral_sum m hm 50
    have hc : ∀ j : ℕ,
        Set.Ioo (((1000 : ℝ) + (j : ℝ)) / 1600) (((1000 : ℝ) + (j : ℝ) + 1) / 1600) =
          Set.Ioo ((50 : ℝ) / 80 + (j : ℝ) / 1600)
            ((50 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600) := by
      intro j
      have hl : (((1000 : ℝ) + (j : ℝ)) / 1600) = (50 : ℝ) / 80 + (j : ℝ) / 1600 := by ring
      have hr : (((1000 : ℝ) + (j : ℝ) + 1) / 1600) = (50 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600 :=
        by
        push_cast
        ring
      rw [hl, hr]
    simp_rw [hc]
    exact h
  have h0 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((1000 : ℝ) + (j : ℝ)) / 1600) (((1000 : ℝ) + (j : ℝ) + 1) / 1600), u ^
        0 * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((1000 : ℝ) + (j : ℝ) + 1) / 1600) ^ 0 *
        hpThetaJensenCellsBatch050Upper j * ((((1000 : ℝ) + (j : ℝ) + 1) / 1600) - (((1000 : ℝ) +
        (j : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch050_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 0
      (Or.inl rfl)).2
  have h2 : (∑ j ∈ Finset.range 20, (((1000 : ℝ) + (j : ℝ)) / 1600) ^ 2 *
    hpThetaJensenCellsBatch050Lower j * ((((1000 : ℝ) + (j : ℝ) + 1) / 1600) - (((1000 : ℝ) + (j :
    ℝ)) / 1600))) ≤
      ∑ j ∈ Finset.range 20,
        ∫ u : ℝ in Set.Ioo (((1000 : ℝ) + (j : ℝ)) / 1600) (((1000 : ℝ) + (j : ℝ) + 1) / 1600), u
          ^ 2 * hpRiemannThetaDifferentialKernel u := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch050_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 2
      (Or.inr (Or.inl rfl))).1
  have h4 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((1000 : ℝ) + (j : ℝ)) / 1600) (((1000 : ℝ) + (j : ℝ) + 1) / 1600), u ^
        4 * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((1000 : ℝ) + (j : ℝ) + 1) / 1600) ^ 4 *
        hpThetaJensenCellsBatch050Upper j * ((((1000 : ℝ) + (j : ℝ) + 1) / 1600) - (((1000 : ℝ) +
        (j : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch050_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 4
      (Or.inr (Or.inr rfl))).2
  rw [hs 0 (Or.inl rfl)] at h0
  rw [hs 2 (Or.inr (Or.inl rfl))] at h2
  rw [hs 4 (Or.inr (Or.inr rfl))] at h4
  norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch050Lower,
    hpThetaJensenCellsBatch050Upper] at h0 h2 h4
  norm_num [hpThetaJensenBatchZeroUpper, hpThetaJensenBatchSecondLower,
    hpThetaJensenBatchFourthUpper]
  exact ⟨le_trans h0 (by norm_num), le_trans (by norm_num) h2,
    le_trans h4 (by norm_num)⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Twenty rational terms are verified for each of the three moment orders.
theorem hpThetaJensenCellsBatch051_finiteIntegral_bounds :
    (∫ u : ℝ in Set.Ioo (51 / 80 : ℝ) ((51 + 1) / 80 : ℝ), u ^ 0 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchZeroUpper 51 ∧
    hpThetaJensenBatchSecondLower 51 ≤
        (∫ u : ℝ in Set.Ioo (51 / 80 : ℝ) ((51 + 1) / 80 : ℝ), u ^ 2 *
          hpRiemannThetaDifferentialKernel u) ∧
    (∫ u : ℝ in Set.Ioo (51 / 80 : ℝ) ((51 + 1) / 80 : ℝ), u ^ 4 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchFourthUpper 51 := by
  have hs (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
      (∑ j ∈ Finset.range 20, ∫ u : ℝ in Set.Ioo (((1020 : ℝ) + (j : ℝ)) / 1600) (((1020 : ℝ) + (j
        : ℝ) + 1) / 1600),
        u ^ m * hpRiemannThetaDifferentialKernel u) =
      ∫ u : ℝ in Set.Ioo (51 / 80 : ℝ) ((51 + 1) / 80 : ℝ), u ^ m *
        hpRiemannThetaDifferentialKernel u := by
    have h := hpThetaJensen_batchCellIntegral_sum m hm 51
    have hc : ∀ j : ℕ,
        Set.Ioo (((1020 : ℝ) + (j : ℝ)) / 1600) (((1020 : ℝ) + (j : ℝ) + 1) / 1600) =
          Set.Ioo ((51 : ℝ) / 80 + (j : ℝ) / 1600)
            ((51 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600) := by
      intro j
      have hl : (((1020 : ℝ) + (j : ℝ)) / 1600) = (51 : ℝ) / 80 + (j : ℝ) / 1600 := by ring
      have hr : (((1020 : ℝ) + (j : ℝ) + 1) / 1600) = (51 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600 :=
        by
        push_cast
        ring
      rw [hl, hr]
    simp_rw [hc]
    exact h
  have h0 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((1020 : ℝ) + (j : ℝ)) / 1600) (((1020 : ℝ) + (j : ℝ) + 1) / 1600), u ^
        0 * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((1020 : ℝ) + (j : ℝ) + 1) / 1600) ^ 0 *
        hpThetaJensenCellsBatch051Upper j * ((((1020 : ℝ) + (j : ℝ) + 1) / 1600) - (((1020 : ℝ) +
        (j : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch051_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 0
      (Or.inl rfl)).2
  have h2 : (∑ j ∈ Finset.range 20, (((1020 : ℝ) + (j : ℝ)) / 1600) ^ 2 *
    hpThetaJensenCellsBatch051Lower j * ((((1020 : ℝ) + (j : ℝ) + 1) / 1600) - (((1020 : ℝ) + (j :
    ℝ)) / 1600))) ≤
      ∑ j ∈ Finset.range 20,
        ∫ u : ℝ in Set.Ioo (((1020 : ℝ) + (j : ℝ)) / 1600) (((1020 : ℝ) + (j : ℝ) + 1) / 1600), u
          ^ 2 * hpRiemannThetaDifferentialKernel u := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch051_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 2
      (Or.inr (Or.inl rfl))).1
  have h4 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((1020 : ℝ) + (j : ℝ)) / 1600) (((1020 : ℝ) + (j : ℝ) + 1) / 1600), u ^
        4 * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((1020 : ℝ) + (j : ℝ) + 1) / 1600) ^ 4 *
        hpThetaJensenCellsBatch051Upper j * ((((1020 : ℝ) + (j : ℝ) + 1) / 1600) - (((1020 : ℝ) +
        (j : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch051_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 4
      (Or.inr (Or.inr rfl))).2
  rw [hs 0 (Or.inl rfl)] at h0
  rw [hs 2 (Or.inr (Or.inl rfl))] at h2
  rw [hs 4 (Or.inr (Or.inr rfl))] at h4
  norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch051Lower,
    hpThetaJensenCellsBatch051Upper] at h0 h2 h4
  norm_num [hpThetaJensenBatchZeroUpper, hpThetaJensenBatchSecondLower,
    hpThetaJensenBatchFourthUpper]
  exact ⟨le_trans h0 (by norm_num), le_trans (by norm_num) h2,
    le_trans h4 (by norm_num)⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Twenty rational terms are verified for each of the three moment orders.
theorem hpThetaJensenCellsBatch052_finiteIntegral_bounds :
    (∫ u : ℝ in Set.Ioo (52 / 80 : ℝ) ((52 + 1) / 80 : ℝ), u ^ 0 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchZeroUpper 52 ∧
    hpThetaJensenBatchSecondLower 52 ≤
        (∫ u : ℝ in Set.Ioo (52 / 80 : ℝ) ((52 + 1) / 80 : ℝ), u ^ 2 *
          hpRiemannThetaDifferentialKernel u) ∧
    (∫ u : ℝ in Set.Ioo (52 / 80 : ℝ) ((52 + 1) / 80 : ℝ), u ^ 4 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchFourthUpper 52 := by
  have hs (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
      (∑ j ∈ Finset.range 20, ∫ u : ℝ in Set.Ioo (((1040 : ℝ) + (j : ℝ)) / 1600) (((1040 : ℝ) + (j
        : ℝ) + 1) / 1600),
        u ^ m * hpRiemannThetaDifferentialKernel u) =
      ∫ u : ℝ in Set.Ioo (52 / 80 : ℝ) ((52 + 1) / 80 : ℝ), u ^ m *
        hpRiemannThetaDifferentialKernel u := by
    have h := hpThetaJensen_batchCellIntegral_sum m hm 52
    have hc : ∀ j : ℕ,
        Set.Ioo (((1040 : ℝ) + (j : ℝ)) / 1600) (((1040 : ℝ) + (j : ℝ) + 1) / 1600) =
          Set.Ioo ((52 : ℝ) / 80 + (j : ℝ) / 1600)
            ((52 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600) := by
      intro j
      have hl : (((1040 : ℝ) + (j : ℝ)) / 1600) = (52 : ℝ) / 80 + (j : ℝ) / 1600 := by ring
      have hr : (((1040 : ℝ) + (j : ℝ) + 1) / 1600) = (52 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600 :=
        by
        push_cast
        ring
      rw [hl, hr]
    simp_rw [hc]
    exact h
  have h0 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((1040 : ℝ) + (j : ℝ)) / 1600) (((1040 : ℝ) + (j : ℝ) + 1) / 1600), u ^
        0 * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((1040 : ℝ) + (j : ℝ) + 1) / 1600) ^ 0 *
        hpThetaJensenCellsBatch052Upper j * ((((1040 : ℝ) + (j : ℝ) + 1) / 1600) - (((1040 : ℝ) +
        (j : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch052_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 0
      (Or.inl rfl)).2
  have h2 : (∑ j ∈ Finset.range 20, (((1040 : ℝ) + (j : ℝ)) / 1600) ^ 2 *
    hpThetaJensenCellsBatch052Lower j * ((((1040 : ℝ) + (j : ℝ) + 1) / 1600) - (((1040 : ℝ) + (j :
    ℝ)) / 1600))) ≤
      ∑ j ∈ Finset.range 20,
        ∫ u : ℝ in Set.Ioo (((1040 : ℝ) + (j : ℝ)) / 1600) (((1040 : ℝ) + (j : ℝ) + 1) / 1600), u
          ^ 2 * hpRiemannThetaDifferentialKernel u := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch052_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 2
      (Or.inr (Or.inl rfl))).1
  have h4 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((1040 : ℝ) + (j : ℝ)) / 1600) (((1040 : ℝ) + (j : ℝ) + 1) / 1600), u ^
        4 * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((1040 : ℝ) + (j : ℝ) + 1) / 1600) ^ 4 *
        hpThetaJensenCellsBatch052Upper j * ((((1040 : ℝ) + (j : ℝ) + 1) / 1600) - (((1040 : ℝ) +
        (j : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch052_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 4
      (Or.inr (Or.inr rfl))).2
  rw [hs 0 (Or.inl rfl)] at h0
  rw [hs 2 (Or.inr (Or.inl rfl))] at h2
  rw [hs 4 (Or.inr (Or.inr rfl))] at h4
  norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch052Lower,
    hpThetaJensenCellsBatch052Upper] at h0 h2 h4
  norm_num [hpThetaJensenBatchZeroUpper, hpThetaJensenBatchSecondLower,
    hpThetaJensenBatchFourthUpper]
  exact ⟨le_trans h0 (by norm_num), le_trans (by norm_num) h2,
    le_trans h4 (by norm_num)⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Twenty rational terms are verified for each of the three moment orders.
theorem hpThetaJensenCellsBatch053_finiteIntegral_bounds :
    (∫ u : ℝ in Set.Ioo (53 / 80 : ℝ) ((53 + 1) / 80 : ℝ), u ^ 0 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchZeroUpper 53 ∧
    hpThetaJensenBatchSecondLower 53 ≤
        (∫ u : ℝ in Set.Ioo (53 / 80 : ℝ) ((53 + 1) / 80 : ℝ), u ^ 2 *
          hpRiemannThetaDifferentialKernel u) ∧
    (∫ u : ℝ in Set.Ioo (53 / 80 : ℝ) ((53 + 1) / 80 : ℝ), u ^ 4 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchFourthUpper 53 := by
  have hs (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
      (∑ j ∈ Finset.range 20, ∫ u : ℝ in Set.Ioo (((1060 : ℝ) + (j : ℝ)) / 1600) (((1060 : ℝ) + (j
        : ℝ) + 1) / 1600),
        u ^ m * hpRiemannThetaDifferentialKernel u) =
      ∫ u : ℝ in Set.Ioo (53 / 80 : ℝ) ((53 + 1) / 80 : ℝ), u ^ m *
        hpRiemannThetaDifferentialKernel u := by
    have h := hpThetaJensen_batchCellIntegral_sum m hm 53
    have hc : ∀ j : ℕ,
        Set.Ioo (((1060 : ℝ) + (j : ℝ)) / 1600) (((1060 : ℝ) + (j : ℝ) + 1) / 1600) =
          Set.Ioo ((53 : ℝ) / 80 + (j : ℝ) / 1600)
            ((53 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600) := by
      intro j
      have hl : (((1060 : ℝ) + (j : ℝ)) / 1600) = (53 : ℝ) / 80 + (j : ℝ) / 1600 := by ring
      have hr : (((1060 : ℝ) + (j : ℝ) + 1) / 1600) = (53 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600 :=
        by
        push_cast
        ring
      rw [hl, hr]
    simp_rw [hc]
    exact h
  have h0 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((1060 : ℝ) + (j : ℝ)) / 1600) (((1060 : ℝ) + (j : ℝ) + 1) / 1600), u ^
        0 * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((1060 : ℝ) + (j : ℝ) + 1) / 1600) ^ 0 *
        hpThetaJensenCellsBatch053Upper j * ((((1060 : ℝ) + (j : ℝ) + 1) / 1600) - (((1060 : ℝ) +
        (j : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch053_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 0
      (Or.inl rfl)).2
  have h2 : (∑ j ∈ Finset.range 20, (((1060 : ℝ) + (j : ℝ)) / 1600) ^ 2 *
    hpThetaJensenCellsBatch053Lower j * ((((1060 : ℝ) + (j : ℝ) + 1) / 1600) - (((1060 : ℝ) + (j :
    ℝ)) / 1600))) ≤
      ∑ j ∈ Finset.range 20,
        ∫ u : ℝ in Set.Ioo (((1060 : ℝ) + (j : ℝ)) / 1600) (((1060 : ℝ) + (j : ℝ) + 1) / 1600), u
          ^ 2 * hpRiemannThetaDifferentialKernel u := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch053_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 2
      (Or.inr (Or.inl rfl))).1
  have h4 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((1060 : ℝ) + (j : ℝ)) / 1600) (((1060 : ℝ) + (j : ℝ) + 1) / 1600), u ^
        4 * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((1060 : ℝ) + (j : ℝ) + 1) / 1600) ^ 4 *
        hpThetaJensenCellsBatch053Upper j * ((((1060 : ℝ) + (j : ℝ) + 1) / 1600) - (((1060 : ℝ) +
        (j : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch053_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 4
      (Or.inr (Or.inr rfl))).2
  rw [hs 0 (Or.inl rfl)] at h0
  rw [hs 2 (Or.inr (Or.inl rfl))] at h2
  rw [hs 4 (Or.inr (Or.inr rfl))] at h4
  norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch053Lower,
    hpThetaJensenCellsBatch053Upper] at h0 h2 h4
  norm_num [hpThetaJensenBatchZeroUpper, hpThetaJensenBatchSecondLower,
    hpThetaJensenBatchFourthUpper]
  exact ⟨le_trans h0 (by norm_num), le_trans (by norm_num) h2,
    le_trans h4 (by norm_num)⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Twenty rational terms are verified for each of the three moment orders.
theorem hpThetaJensenCellsBatch054_finiteIntegral_bounds :
    (∫ u : ℝ in Set.Ioo (54 / 80 : ℝ) ((54 + 1) / 80 : ℝ), u ^ 0 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchZeroUpper 54 ∧
    hpThetaJensenBatchSecondLower 54 ≤
        (∫ u : ℝ in Set.Ioo (54 / 80 : ℝ) ((54 + 1) / 80 : ℝ), u ^ 2 *
          hpRiemannThetaDifferentialKernel u) ∧
    (∫ u : ℝ in Set.Ioo (54 / 80 : ℝ) ((54 + 1) / 80 : ℝ), u ^ 4 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchFourthUpper 54 := by
  have hs (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
      (∑ j ∈ Finset.range 20, ∫ u : ℝ in Set.Ioo (((1080 : ℝ) + (j : ℝ)) / 1600) (((1080 : ℝ) + (j
        : ℝ) + 1) / 1600),
        u ^ m * hpRiemannThetaDifferentialKernel u) =
      ∫ u : ℝ in Set.Ioo (54 / 80 : ℝ) ((54 + 1) / 80 : ℝ), u ^ m *
        hpRiemannThetaDifferentialKernel u := by
    have h := hpThetaJensen_batchCellIntegral_sum m hm 54
    have hc : ∀ j : ℕ,
        Set.Ioo (((1080 : ℝ) + (j : ℝ)) / 1600) (((1080 : ℝ) + (j : ℝ) + 1) / 1600) =
          Set.Ioo ((54 : ℝ) / 80 + (j : ℝ) / 1600)
            ((54 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600) := by
      intro j
      have hl : (((1080 : ℝ) + (j : ℝ)) / 1600) = (54 : ℝ) / 80 + (j : ℝ) / 1600 := by ring
      have hr : (((1080 : ℝ) + (j : ℝ) + 1) / 1600) = (54 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600 :=
        by
        push_cast
        ring
      rw [hl, hr]
    simp_rw [hc]
    exact h
  have h0 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((1080 : ℝ) + (j : ℝ)) / 1600) (((1080 : ℝ) + (j : ℝ) + 1) / 1600), u ^
        0 * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((1080 : ℝ) + (j : ℝ) + 1) / 1600) ^ 0 *
        hpThetaJensenCellsBatch054Upper j * ((((1080 : ℝ) + (j : ℝ) + 1) / 1600) - (((1080 : ℝ) +
        (j : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch054_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 0
      (Or.inl rfl)).2
  have h2 : (∑ j ∈ Finset.range 20, (((1080 : ℝ) + (j : ℝ)) / 1600) ^ 2 *
    hpThetaJensenCellsBatch054Lower j * ((((1080 : ℝ) + (j : ℝ) + 1) / 1600) - (((1080 : ℝ) + (j :
    ℝ)) / 1600))) ≤
      ∑ j ∈ Finset.range 20,
        ∫ u : ℝ in Set.Ioo (((1080 : ℝ) + (j : ℝ)) / 1600) (((1080 : ℝ) + (j : ℝ) + 1) / 1600), u
          ^ 2 * hpRiemannThetaDifferentialKernel u := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch054_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 2
      (Or.inr (Or.inl rfl))).1
  have h4 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((1080 : ℝ) + (j : ℝ)) / 1600) (((1080 : ℝ) + (j : ℝ) + 1) / 1600), u ^
        4 * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((1080 : ℝ) + (j : ℝ) + 1) / 1600) ^ 4 *
        hpThetaJensenCellsBatch054Upper j * ((((1080 : ℝ) + (j : ℝ) + 1) / 1600) - (((1080 : ℝ) +
        (j : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch054_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 4
      (Or.inr (Or.inr rfl))).2
  rw [hs 0 (Or.inl rfl)] at h0
  rw [hs 2 (Or.inr (Or.inl rfl))] at h2
  rw [hs 4 (Or.inr (Or.inr rfl))] at h4
  norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch054Lower,
    hpThetaJensenCellsBatch054Upper] at h0 h2 h4
  norm_num [hpThetaJensenBatchZeroUpper, hpThetaJensenBatchSecondLower,
    hpThetaJensenBatchFourthUpper]
  exact ⟨le_trans h0 (by norm_num), le_trans (by norm_num) h2,
    le_trans h4 (by norm_num)⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Twenty rational terms are verified for each of the three moment orders.
theorem hpThetaJensenCellsBatch055_finiteIntegral_bounds :
    (∫ u : ℝ in Set.Ioo (55 / 80 : ℝ) ((55 + 1) / 80 : ℝ), u ^ 0 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchZeroUpper 55 ∧
    hpThetaJensenBatchSecondLower 55 ≤
        (∫ u : ℝ in Set.Ioo (55 / 80 : ℝ) ((55 + 1) / 80 : ℝ), u ^ 2 *
          hpRiemannThetaDifferentialKernel u) ∧
    (∫ u : ℝ in Set.Ioo (55 / 80 : ℝ) ((55 + 1) / 80 : ℝ), u ^ 4 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchFourthUpper 55 := by
  have hs (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
      (∑ j ∈ Finset.range 20, ∫ u : ℝ in Set.Ioo (((1100 : ℝ) + (j : ℝ)) / 1600) (((1100 : ℝ) + (j
        : ℝ) + 1) / 1600),
        u ^ m * hpRiemannThetaDifferentialKernel u) =
      ∫ u : ℝ in Set.Ioo (55 / 80 : ℝ) ((55 + 1) / 80 : ℝ), u ^ m *
        hpRiemannThetaDifferentialKernel u := by
    have h := hpThetaJensen_batchCellIntegral_sum m hm 55
    have hc : ∀ j : ℕ,
        Set.Ioo (((1100 : ℝ) + (j : ℝ)) / 1600) (((1100 : ℝ) + (j : ℝ) + 1) / 1600) =
          Set.Ioo ((55 : ℝ) / 80 + (j : ℝ) / 1600)
            ((55 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600) := by
      intro j
      have hl : (((1100 : ℝ) + (j : ℝ)) / 1600) = (55 : ℝ) / 80 + (j : ℝ) / 1600 := by ring
      have hr : (((1100 : ℝ) + (j : ℝ) + 1) / 1600) = (55 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600 :=
        by
        push_cast
        ring
      rw [hl, hr]
    simp_rw [hc]
    exact h
  have h0 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((1100 : ℝ) + (j : ℝ)) / 1600) (((1100 : ℝ) + (j : ℝ) + 1) / 1600), u ^
        0 * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((1100 : ℝ) + (j : ℝ) + 1) / 1600) ^ 0 *
        hpThetaJensenCellsBatch055Upper j * ((((1100 : ℝ) + (j : ℝ) + 1) / 1600) - (((1100 : ℝ) +
        (j : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch055_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 0
      (Or.inl rfl)).2
  have h2 : (∑ j ∈ Finset.range 20, (((1100 : ℝ) + (j : ℝ)) / 1600) ^ 2 *
    hpThetaJensenCellsBatch055Lower j * ((((1100 : ℝ) + (j : ℝ) + 1) / 1600) - (((1100 : ℝ) + (j :
    ℝ)) / 1600))) ≤
      ∑ j ∈ Finset.range 20,
        ∫ u : ℝ in Set.Ioo (((1100 : ℝ) + (j : ℝ)) / 1600) (((1100 : ℝ) + (j : ℝ) + 1) / 1600), u
          ^ 2 * hpRiemannThetaDifferentialKernel u := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch055_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 2
      (Or.inr (Or.inl rfl))).1
  have h4 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((1100 : ℝ) + (j : ℝ)) / 1600) (((1100 : ℝ) + (j : ℝ) + 1) / 1600), u ^
        4 * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((1100 : ℝ) + (j : ℝ) + 1) / 1600) ^ 4 *
        hpThetaJensenCellsBatch055Upper j * ((((1100 : ℝ) + (j : ℝ) + 1) / 1600) - (((1100 : ℝ) +
        (j : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch055_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 4
      (Or.inr (Or.inr rfl))).2
  rw [hs 0 (Or.inl rfl)] at h0
  rw [hs 2 (Or.inr (Or.inl rfl))] at h2
  rw [hs 4 (Or.inr (Or.inr rfl))] at h4
  norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch055Lower,
    hpThetaJensenCellsBatch055Upper] at h0 h2 h4
  norm_num [hpThetaJensenBatchZeroUpper, hpThetaJensenBatchSecondLower,
    hpThetaJensenBatchFourthUpper]
  exact ⟨le_trans h0 (by norm_num), le_trans (by norm_num) h2,
    le_trans h4 (by norm_num)⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Twenty rational terms are verified for each of the three moment orders.
theorem hpThetaJensenCellsBatch056_finiteIntegral_bounds :
    (∫ u : ℝ in Set.Ioo (56 / 80 : ℝ) ((56 + 1) / 80 : ℝ), u ^ 0 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchZeroUpper 56 ∧
    hpThetaJensenBatchSecondLower 56 ≤
        (∫ u : ℝ in Set.Ioo (56 / 80 : ℝ) ((56 + 1) / 80 : ℝ), u ^ 2 *
          hpRiemannThetaDifferentialKernel u) ∧
    (∫ u : ℝ in Set.Ioo (56 / 80 : ℝ) ((56 + 1) / 80 : ℝ), u ^ 4 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchFourthUpper 56 := by
  have hs (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
      (∑ j ∈ Finset.range 20, ∫ u : ℝ in Set.Ioo (((1120 : ℝ) + (j : ℝ)) / 1600) (((1120 : ℝ) + (j
        : ℝ) + 1) / 1600),
        u ^ m * hpRiemannThetaDifferentialKernel u) =
      ∫ u : ℝ in Set.Ioo (56 / 80 : ℝ) ((56 + 1) / 80 : ℝ), u ^ m *
        hpRiemannThetaDifferentialKernel u := by
    have h := hpThetaJensen_batchCellIntegral_sum m hm 56
    have hc : ∀ j : ℕ,
        Set.Ioo (((1120 : ℝ) + (j : ℝ)) / 1600) (((1120 : ℝ) + (j : ℝ) + 1) / 1600) =
          Set.Ioo ((56 : ℝ) / 80 + (j : ℝ) / 1600)
            ((56 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600) := by
      intro j
      have hl : (((1120 : ℝ) + (j : ℝ)) / 1600) = (56 : ℝ) / 80 + (j : ℝ) / 1600 := by ring
      have hr : (((1120 : ℝ) + (j : ℝ) + 1) / 1600) = (56 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600 :=
        by
        push_cast
        ring
      rw [hl, hr]
    simp_rw [hc]
    exact h
  have h0 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((1120 : ℝ) + (j : ℝ)) / 1600) (((1120 : ℝ) + (j : ℝ) + 1) / 1600), u ^
        0 * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((1120 : ℝ) + (j : ℝ) + 1) / 1600) ^ 0 *
        hpThetaJensenCellsBatch056Upper j * ((((1120 : ℝ) + (j : ℝ) + 1) / 1600) - (((1120 : ℝ) +
        (j : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch056_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 0
      (Or.inl rfl)).2
  have h2 : (∑ j ∈ Finset.range 20, (((1120 : ℝ) + (j : ℝ)) / 1600) ^ 2 *
    hpThetaJensenCellsBatch056Lower j * ((((1120 : ℝ) + (j : ℝ) + 1) / 1600) - (((1120 : ℝ) + (j :
    ℝ)) / 1600))) ≤
      ∑ j ∈ Finset.range 20,
        ∫ u : ℝ in Set.Ioo (((1120 : ℝ) + (j : ℝ)) / 1600) (((1120 : ℝ) + (j : ℝ) + 1) / 1600), u
          ^ 2 * hpRiemannThetaDifferentialKernel u := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch056_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 2
      (Or.inr (Or.inl rfl))).1
  have h4 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((1120 : ℝ) + (j : ℝ)) / 1600) (((1120 : ℝ) + (j : ℝ) + 1) / 1600), u ^
        4 * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((1120 : ℝ) + (j : ℝ) + 1) / 1600) ^ 4 *
        hpThetaJensenCellsBatch056Upper j * ((((1120 : ℝ) + (j : ℝ) + 1) / 1600) - (((1120 : ℝ) +
        (j : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch056_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 4
      (Or.inr (Or.inr rfl))).2
  rw [hs 0 (Or.inl rfl)] at h0
  rw [hs 2 (Or.inr (Or.inl rfl))] at h2
  rw [hs 4 (Or.inr (Or.inr rfl))] at h4
  norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch056Lower,
    hpThetaJensenCellsBatch056Upper] at h0 h2 h4
  norm_num [hpThetaJensenBatchZeroUpper, hpThetaJensenBatchSecondLower,
    hpThetaJensenBatchFourthUpper]
  exact ⟨le_trans h0 (by norm_num), le_trans (by norm_num) h2,
    le_trans h4 (by norm_num)⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Twenty rational terms are verified for each of the three moment orders.
theorem hpThetaJensenCellsBatch057_finiteIntegral_bounds :
    (∫ u : ℝ in Set.Ioo (57 / 80 : ℝ) ((57 + 1) / 80 : ℝ), u ^ 0 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchZeroUpper 57 ∧
    hpThetaJensenBatchSecondLower 57 ≤
        (∫ u : ℝ in Set.Ioo (57 / 80 : ℝ) ((57 + 1) / 80 : ℝ), u ^ 2 *
          hpRiemannThetaDifferentialKernel u) ∧
    (∫ u : ℝ in Set.Ioo (57 / 80 : ℝ) ((57 + 1) / 80 : ℝ), u ^ 4 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchFourthUpper 57 := by
  have hs (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
      (∑ j ∈ Finset.range 20, ∫ u : ℝ in Set.Ioo (((1140 : ℝ) + (j : ℝ)) / 1600) (((1140 : ℝ) + (j
        : ℝ) + 1) / 1600),
        u ^ m * hpRiemannThetaDifferentialKernel u) =
      ∫ u : ℝ in Set.Ioo (57 / 80 : ℝ) ((57 + 1) / 80 : ℝ), u ^ m *
        hpRiemannThetaDifferentialKernel u := by
    have h := hpThetaJensen_batchCellIntegral_sum m hm 57
    have hc : ∀ j : ℕ,
        Set.Ioo (((1140 : ℝ) + (j : ℝ)) / 1600) (((1140 : ℝ) + (j : ℝ) + 1) / 1600) =
          Set.Ioo ((57 : ℝ) / 80 + (j : ℝ) / 1600)
            ((57 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600) := by
      intro j
      have hl : (((1140 : ℝ) + (j : ℝ)) / 1600) = (57 : ℝ) / 80 + (j : ℝ) / 1600 := by ring
      have hr : (((1140 : ℝ) + (j : ℝ) + 1) / 1600) = (57 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600 :=
        by
        push_cast
        ring
      rw [hl, hr]
    simp_rw [hc]
    exact h
  have h0 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((1140 : ℝ) + (j : ℝ)) / 1600) (((1140 : ℝ) + (j : ℝ) + 1) / 1600), u ^
        0 * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((1140 : ℝ) + (j : ℝ) + 1) / 1600) ^ 0 *
        hpThetaJensenCellsBatch057Upper j * ((((1140 : ℝ) + (j : ℝ) + 1) / 1600) - (((1140 : ℝ) +
        (j : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch057_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 0
      (Or.inl rfl)).2
  have h2 : (∑ j ∈ Finset.range 20, (((1140 : ℝ) + (j : ℝ)) / 1600) ^ 2 *
    hpThetaJensenCellsBatch057Lower j * ((((1140 : ℝ) + (j : ℝ) + 1) / 1600) - (((1140 : ℝ) + (j :
    ℝ)) / 1600))) ≤
      ∑ j ∈ Finset.range 20,
        ∫ u : ℝ in Set.Ioo (((1140 : ℝ) + (j : ℝ)) / 1600) (((1140 : ℝ) + (j : ℝ) + 1) / 1600), u
          ^ 2 * hpRiemannThetaDifferentialKernel u := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch057_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 2
      (Or.inr (Or.inl rfl))).1
  have h4 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((1140 : ℝ) + (j : ℝ)) / 1600) (((1140 : ℝ) + (j : ℝ) + 1) / 1600), u ^
        4 * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((1140 : ℝ) + (j : ℝ) + 1) / 1600) ^ 4 *
        hpThetaJensenCellsBatch057Upper j * ((((1140 : ℝ) + (j : ℝ) + 1) / 1600) - (((1140 : ℝ) +
        (j : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch057_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 4
      (Or.inr (Or.inr rfl))).2
  rw [hs 0 (Or.inl rfl)] at h0
  rw [hs 2 (Or.inr (Or.inl rfl))] at h2
  rw [hs 4 (Or.inr (Or.inr rfl))] at h4
  norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch057Lower,
    hpThetaJensenCellsBatch057Upper] at h0 h2 h4
  norm_num [hpThetaJensenBatchZeroUpper, hpThetaJensenBatchSecondLower,
    hpThetaJensenBatchFourthUpper]
  exact ⟨le_trans h0 (by norm_num), le_trans (by norm_num) h2,
    le_trans h4 (by norm_num)⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Twenty rational terms are verified for each of the three moment orders.
theorem hpThetaJensenCellsBatch058_finiteIntegral_bounds :
    (∫ u : ℝ in Set.Ioo (58 / 80 : ℝ) ((58 + 1) / 80 : ℝ), u ^ 0 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchZeroUpper 58 ∧
    hpThetaJensenBatchSecondLower 58 ≤
        (∫ u : ℝ in Set.Ioo (58 / 80 : ℝ) ((58 + 1) / 80 : ℝ), u ^ 2 *
          hpRiemannThetaDifferentialKernel u) ∧
    (∫ u : ℝ in Set.Ioo (58 / 80 : ℝ) ((58 + 1) / 80 : ℝ), u ^ 4 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchFourthUpper 58 := by
  have hs (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
      (∑ j ∈ Finset.range 20, ∫ u : ℝ in Set.Ioo (((1160 : ℝ) + (j : ℝ)) / 1600) (((1160 : ℝ) + (j
        : ℝ) + 1) / 1600),
        u ^ m * hpRiemannThetaDifferentialKernel u) =
      ∫ u : ℝ in Set.Ioo (58 / 80 : ℝ) ((58 + 1) / 80 : ℝ), u ^ m *
        hpRiemannThetaDifferentialKernel u := by
    have h := hpThetaJensen_batchCellIntegral_sum m hm 58
    have hc : ∀ j : ℕ,
        Set.Ioo (((1160 : ℝ) + (j : ℝ)) / 1600) (((1160 : ℝ) + (j : ℝ) + 1) / 1600) =
          Set.Ioo ((58 : ℝ) / 80 + (j : ℝ) / 1600)
            ((58 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600) := by
      intro j
      have hl : (((1160 : ℝ) + (j : ℝ)) / 1600) = (58 : ℝ) / 80 + (j : ℝ) / 1600 := by ring
      have hr : (((1160 : ℝ) + (j : ℝ) + 1) / 1600) = (58 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600 :=
        by
        push_cast
        ring
      rw [hl, hr]
    simp_rw [hc]
    exact h
  have h0 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((1160 : ℝ) + (j : ℝ)) / 1600) (((1160 : ℝ) + (j : ℝ) + 1) / 1600), u ^
        0 * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((1160 : ℝ) + (j : ℝ) + 1) / 1600) ^ 0 *
        hpThetaJensenCellsBatch058Upper j * ((((1160 : ℝ) + (j : ℝ) + 1) / 1600) - (((1160 : ℝ) +
        (j : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch058_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 0
      (Or.inl rfl)).2
  have h2 : (∑ j ∈ Finset.range 20, (((1160 : ℝ) + (j : ℝ)) / 1600) ^ 2 *
    hpThetaJensenCellsBatch058Lower j * ((((1160 : ℝ) + (j : ℝ) + 1) / 1600) - (((1160 : ℝ) + (j :
    ℝ)) / 1600))) ≤
      ∑ j ∈ Finset.range 20,
        ∫ u : ℝ in Set.Ioo (((1160 : ℝ) + (j : ℝ)) / 1600) (((1160 : ℝ) + (j : ℝ) + 1) / 1600), u
          ^ 2 * hpRiemannThetaDifferentialKernel u := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch058_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 2
      (Or.inr (Or.inl rfl))).1
  have h4 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((1160 : ℝ) + (j : ℝ)) / 1600) (((1160 : ℝ) + (j : ℝ) + 1) / 1600), u ^
        4 * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((1160 : ℝ) + (j : ℝ) + 1) / 1600) ^ 4 *
        hpThetaJensenCellsBatch058Upper j * ((((1160 : ℝ) + (j : ℝ) + 1) / 1600) - (((1160 : ℝ) +
        (j : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch058_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 4
      (Or.inr (Or.inr rfl))).2
  rw [hs 0 (Or.inl rfl)] at h0
  rw [hs 2 (Or.inr (Or.inl rfl))] at h2
  rw [hs 4 (Or.inr (Or.inr rfl))] at h4
  norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch058Lower,
    hpThetaJensenCellsBatch058Upper] at h0 h2 h4
  norm_num [hpThetaJensenBatchZeroUpper, hpThetaJensenBatchSecondLower,
    hpThetaJensenBatchFourthUpper]
  exact ⟨le_trans h0 (by norm_num), le_trans (by norm_num) h2,
    le_trans h4 (by norm_num)⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Twenty rational terms are verified for each of the three moment orders.
theorem hpThetaJensenCellsBatch059_finiteIntegral_bounds :
    (∫ u : ℝ in Set.Ioo (59 / 80 : ℝ) ((59 + 1) / 80 : ℝ), u ^ 0 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchZeroUpper 59 ∧
    hpThetaJensenBatchSecondLower 59 ≤
        (∫ u : ℝ in Set.Ioo (59 / 80 : ℝ) ((59 + 1) / 80 : ℝ), u ^ 2 *
          hpRiemannThetaDifferentialKernel u) ∧
    (∫ u : ℝ in Set.Ioo (59 / 80 : ℝ) ((59 + 1) / 80 : ℝ), u ^ 4 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchFourthUpper 59 := by
  have hs (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
      (∑ j ∈ Finset.range 20, ∫ u : ℝ in Set.Ioo (((1180 : ℝ) + (j : ℝ)) / 1600) (((1180 : ℝ) + (j
        : ℝ) + 1) / 1600),
        u ^ m * hpRiemannThetaDifferentialKernel u) =
      ∫ u : ℝ in Set.Ioo (59 / 80 : ℝ) ((59 + 1) / 80 : ℝ), u ^ m *
        hpRiemannThetaDifferentialKernel u := by
    have h := hpThetaJensen_batchCellIntegral_sum m hm 59
    have hc : ∀ j : ℕ,
        Set.Ioo (((1180 : ℝ) + (j : ℝ)) / 1600) (((1180 : ℝ) + (j : ℝ) + 1) / 1600) =
          Set.Ioo ((59 : ℝ) / 80 + (j : ℝ) / 1600)
            ((59 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600) := by
      intro j
      have hl : (((1180 : ℝ) + (j : ℝ)) / 1600) = (59 : ℝ) / 80 + (j : ℝ) / 1600 := by ring
      have hr : (((1180 : ℝ) + (j : ℝ) + 1) / 1600) = (59 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600 :=
        by
        push_cast
        ring
      rw [hl, hr]
    simp_rw [hc]
    exact h
  have h0 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((1180 : ℝ) + (j : ℝ)) / 1600) (((1180 : ℝ) + (j : ℝ) + 1) / 1600), u ^
        0 * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((1180 : ℝ) + (j : ℝ) + 1) / 1600) ^ 0 *
        hpThetaJensenCellsBatch059Upper j * ((((1180 : ℝ) + (j : ℝ) + 1) / 1600) - (((1180 : ℝ) +
        (j : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch059_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 0
      (Or.inl rfl)).2
  have h2 : (∑ j ∈ Finset.range 20, (((1180 : ℝ) + (j : ℝ)) / 1600) ^ 2 *
    hpThetaJensenCellsBatch059Lower j * ((((1180 : ℝ) + (j : ℝ) + 1) / 1600) - (((1180 : ℝ) + (j :
    ℝ)) / 1600))) ≤
      ∑ j ∈ Finset.range 20,
        ∫ u : ℝ in Set.Ioo (((1180 : ℝ) + (j : ℝ)) / 1600) (((1180 : ℝ) + (j : ℝ) + 1) / 1600), u
          ^ 2 * hpRiemannThetaDifferentialKernel u := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch059_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 2
      (Or.inr (Or.inl rfl))).1
  have h4 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((1180 : ℝ) + (j : ℝ)) / 1600) (((1180 : ℝ) + (j : ℝ) + 1) / 1600), u ^
        4 * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((1180 : ℝ) + (j : ℝ) + 1) / 1600) ^ 4 *
        hpThetaJensenCellsBatch059Upper j * ((((1180 : ℝ) + (j : ℝ) + 1) / 1600) - (((1180 : ℝ) +
        (j : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch059_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 4
      (Or.inr (Or.inr rfl))).2
  rw [hs 0 (Or.inl rfl)] at h0
  rw [hs 2 (Or.inr (Or.inl rfl))] at h2
  rw [hs 4 (Or.inr (Or.inr rfl))] at h4
  norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch059Lower,
    hpThetaJensenCellsBatch059Upper] at h0 h2 h4
  norm_num [hpThetaJensenBatchZeroUpper, hpThetaJensenBatchSecondLower,
    hpThetaJensenBatchFourthUpper]
  exact ⟨le_trans h0 (by norm_num), le_trans (by norm_num) h2,
    le_trans h4 (by norm_num)⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Twenty rational terms are verified for each of the three moment orders.
theorem hpThetaJensenCellsBatch060_finiteIntegral_bounds :
    (∫ u : ℝ in Set.Ioo (60 / 80 : ℝ) ((60 + 1) / 80 : ℝ), u ^ 0 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchZeroUpper 60 ∧
    hpThetaJensenBatchSecondLower 60 ≤
        (∫ u : ℝ in Set.Ioo (60 / 80 : ℝ) ((60 + 1) / 80 : ℝ), u ^ 2 *
          hpRiemannThetaDifferentialKernel u) ∧
    (∫ u : ℝ in Set.Ioo (60 / 80 : ℝ) ((60 + 1) / 80 : ℝ), u ^ 4 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchFourthUpper 60 := by
  have hs (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
      (∑ j ∈ Finset.range 20, ∫ u : ℝ in Set.Ioo (((1200 : ℝ) + (j : ℝ)) / 1600) (((1200 : ℝ) + (j
        : ℝ) + 1) / 1600),
        u ^ m * hpRiemannThetaDifferentialKernel u) =
      ∫ u : ℝ in Set.Ioo (60 / 80 : ℝ) ((60 + 1) / 80 : ℝ), u ^ m *
        hpRiemannThetaDifferentialKernel u := by
    have h := hpThetaJensen_batchCellIntegral_sum m hm 60
    have hc : ∀ j : ℕ,
        Set.Ioo (((1200 : ℝ) + (j : ℝ)) / 1600) (((1200 : ℝ) + (j : ℝ) + 1) / 1600) =
          Set.Ioo ((60 : ℝ) / 80 + (j : ℝ) / 1600)
            ((60 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600) := by
      intro j
      have hl : (((1200 : ℝ) + (j : ℝ)) / 1600) = (60 : ℝ) / 80 + (j : ℝ) / 1600 := by ring
      have hr : (((1200 : ℝ) + (j : ℝ) + 1) / 1600) = (60 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600 :=
        by
        push_cast
        ring
      rw [hl, hr]
    simp_rw [hc]
    exact h
  have h0 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((1200 : ℝ) + (j : ℝ)) / 1600) (((1200 : ℝ) + (j : ℝ) + 1) / 1600), u ^
        0 * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((1200 : ℝ) + (j : ℝ) + 1) / 1600) ^ 0 *
        hpThetaJensenCellsBatch060Upper j * ((((1200 : ℝ) + (j : ℝ) + 1) / 1600) - (((1200 : ℝ) +
        (j : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch060_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 0
      (Or.inl rfl)).2
  have h2 : (∑ j ∈ Finset.range 20, (((1200 : ℝ) + (j : ℝ)) / 1600) ^ 2 *
    hpThetaJensenCellsBatch060Lower j * ((((1200 : ℝ) + (j : ℝ) + 1) / 1600) - (((1200 : ℝ) + (j :
    ℝ)) / 1600))) ≤
      ∑ j ∈ Finset.range 20,
        ∫ u : ℝ in Set.Ioo (((1200 : ℝ) + (j : ℝ)) / 1600) (((1200 : ℝ) + (j : ℝ) + 1) / 1600), u
          ^ 2 * hpRiemannThetaDifferentialKernel u := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch060_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 2
      (Or.inr (Or.inl rfl))).1
  have h4 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((1200 : ℝ) + (j : ℝ)) / 1600) (((1200 : ℝ) + (j : ℝ) + 1) / 1600), u ^
        4 * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((1200 : ℝ) + (j : ℝ) + 1) / 1600) ^ 4 *
        hpThetaJensenCellsBatch060Upper j * ((((1200 : ℝ) + (j : ℝ) + 1) / 1600) - (((1200 : ℝ) +
        (j : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch060_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 4
      (Or.inr (Or.inr rfl))).2
  rw [hs 0 (Or.inl rfl)] at h0
  rw [hs 2 (Or.inr (Or.inl rfl))] at h2
  rw [hs 4 (Or.inr (Or.inr rfl))] at h4
  norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch060Lower,
    hpThetaJensenCellsBatch060Upper] at h0 h2 h4
  norm_num [hpThetaJensenBatchZeroUpper, hpThetaJensenBatchSecondLower,
    hpThetaJensenBatchFourthUpper]
  exact ⟨le_trans h0 (by norm_num), le_trans (by norm_num) h2,
    le_trans h4 (by norm_num)⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Twenty rational terms are verified for each of the three moment orders.
theorem hpThetaJensenCellsBatch061_finiteIntegral_bounds :
    (∫ u : ℝ in Set.Ioo (61 / 80 : ℝ) ((61 + 1) / 80 : ℝ), u ^ 0 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchZeroUpper 61 ∧
    hpThetaJensenBatchSecondLower 61 ≤
        (∫ u : ℝ in Set.Ioo (61 / 80 : ℝ) ((61 + 1) / 80 : ℝ), u ^ 2 *
          hpRiemannThetaDifferentialKernel u) ∧
    (∫ u : ℝ in Set.Ioo (61 / 80 : ℝ) ((61 + 1) / 80 : ℝ), u ^ 4 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchFourthUpper 61 := by
  have hs (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
      (∑ j ∈ Finset.range 20, ∫ u : ℝ in Set.Ioo (((1220 : ℝ) + (j : ℝ)) / 1600) (((1220 : ℝ) + (j
        : ℝ) + 1) / 1600),
        u ^ m * hpRiemannThetaDifferentialKernel u) =
      ∫ u : ℝ in Set.Ioo (61 / 80 : ℝ) ((61 + 1) / 80 : ℝ), u ^ m *
        hpRiemannThetaDifferentialKernel u := by
    have h := hpThetaJensen_batchCellIntegral_sum m hm 61
    have hc : ∀ j : ℕ,
        Set.Ioo (((1220 : ℝ) + (j : ℝ)) / 1600) (((1220 : ℝ) + (j : ℝ) + 1) / 1600) =
          Set.Ioo ((61 : ℝ) / 80 + (j : ℝ) / 1600)
            ((61 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600) := by
      intro j
      have hl : (((1220 : ℝ) + (j : ℝ)) / 1600) = (61 : ℝ) / 80 + (j : ℝ) / 1600 := by ring
      have hr : (((1220 : ℝ) + (j : ℝ) + 1) / 1600) = (61 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600 :=
        by
        push_cast
        ring
      rw [hl, hr]
    simp_rw [hc]
    exact h
  have h0 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((1220 : ℝ) + (j : ℝ)) / 1600) (((1220 : ℝ) + (j : ℝ) + 1) / 1600), u ^
        0 * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((1220 : ℝ) + (j : ℝ) + 1) / 1600) ^ 0 *
        hpThetaJensenCellsBatch061Upper j * ((((1220 : ℝ) + (j : ℝ) + 1) / 1600) - (((1220 : ℝ) +
        (j : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch061_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 0
      (Or.inl rfl)).2
  have h2 : (∑ j ∈ Finset.range 20, (((1220 : ℝ) + (j : ℝ)) / 1600) ^ 2 *
    hpThetaJensenCellsBatch061Lower j * ((((1220 : ℝ) + (j : ℝ) + 1) / 1600) - (((1220 : ℝ) + (j :
    ℝ)) / 1600))) ≤
      ∑ j ∈ Finset.range 20,
        ∫ u : ℝ in Set.Ioo (((1220 : ℝ) + (j : ℝ)) / 1600) (((1220 : ℝ) + (j : ℝ) + 1) / 1600), u
          ^ 2 * hpRiemannThetaDifferentialKernel u := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch061_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 2
      (Or.inr (Or.inl rfl))).1
  have h4 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((1220 : ℝ) + (j : ℝ)) / 1600) (((1220 : ℝ) + (j : ℝ) + 1) / 1600), u ^
        4 * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((1220 : ℝ) + (j : ℝ) + 1) / 1600) ^ 4 *
        hpThetaJensenCellsBatch061Upper j * ((((1220 : ℝ) + (j : ℝ) + 1) / 1600) - (((1220 : ℝ) +
        (j : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch061_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 4
      (Or.inr (Or.inr rfl))).2
  rw [hs 0 (Or.inl rfl)] at h0
  rw [hs 2 (Or.inr (Or.inl rfl))] at h2
  rw [hs 4 (Or.inr (Or.inr rfl))] at h4
  norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch061Lower,
    hpThetaJensenCellsBatch061Upper] at h0 h2 h4
  norm_num [hpThetaJensenBatchZeroUpper, hpThetaJensenBatchSecondLower,
    hpThetaJensenBatchFourthUpper]
  exact ⟨le_trans h0 (by norm_num), le_trans (by norm_num) h2,
    le_trans h4 (by norm_num)⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Twenty rational terms are verified for each of the three moment orders.
theorem hpThetaJensenCellsBatch062_finiteIntegral_bounds :
    (∫ u : ℝ in Set.Ioo (62 / 80 : ℝ) ((62 + 1) / 80 : ℝ), u ^ 0 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchZeroUpper 62 ∧
    hpThetaJensenBatchSecondLower 62 ≤
        (∫ u : ℝ in Set.Ioo (62 / 80 : ℝ) ((62 + 1) / 80 : ℝ), u ^ 2 *
          hpRiemannThetaDifferentialKernel u) ∧
    (∫ u : ℝ in Set.Ioo (62 / 80 : ℝ) ((62 + 1) / 80 : ℝ), u ^ 4 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchFourthUpper 62 := by
  have hs (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
      (∑ j ∈ Finset.range 20, ∫ u : ℝ in Set.Ioo (((1240 : ℝ) + (j : ℝ)) / 1600) (((1240 : ℝ) + (j
        : ℝ) + 1) / 1600),
        u ^ m * hpRiemannThetaDifferentialKernel u) =
      ∫ u : ℝ in Set.Ioo (62 / 80 : ℝ) ((62 + 1) / 80 : ℝ), u ^ m *
        hpRiemannThetaDifferentialKernel u := by
    have h := hpThetaJensen_batchCellIntegral_sum m hm 62
    have hc : ∀ j : ℕ,
        Set.Ioo (((1240 : ℝ) + (j : ℝ)) / 1600) (((1240 : ℝ) + (j : ℝ) + 1) / 1600) =
          Set.Ioo ((62 : ℝ) / 80 + (j : ℝ) / 1600)
            ((62 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600) := by
      intro j
      have hl : (((1240 : ℝ) + (j : ℝ)) / 1600) = (62 : ℝ) / 80 + (j : ℝ) / 1600 := by ring
      have hr : (((1240 : ℝ) + (j : ℝ) + 1) / 1600) = (62 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600 :=
        by
        push_cast
        ring
      rw [hl, hr]
    simp_rw [hc]
    exact h
  have h0 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((1240 : ℝ) + (j : ℝ)) / 1600) (((1240 : ℝ) + (j : ℝ) + 1) / 1600), u ^
        0 * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((1240 : ℝ) + (j : ℝ) + 1) / 1600) ^ 0 *
        hpThetaJensenCellsBatch062Upper j * ((((1240 : ℝ) + (j : ℝ) + 1) / 1600) - (((1240 : ℝ) +
        (j : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch062_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 0
      (Or.inl rfl)).2
  have h2 : (∑ j ∈ Finset.range 20, (((1240 : ℝ) + (j : ℝ)) / 1600) ^ 2 *
    hpThetaJensenCellsBatch062Lower j * ((((1240 : ℝ) + (j : ℝ) + 1) / 1600) - (((1240 : ℝ) + (j :
    ℝ)) / 1600))) ≤
      ∑ j ∈ Finset.range 20,
        ∫ u : ℝ in Set.Ioo (((1240 : ℝ) + (j : ℝ)) / 1600) (((1240 : ℝ) + (j : ℝ) + 1) / 1600), u
          ^ 2 * hpRiemannThetaDifferentialKernel u := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch062_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 2
      (Or.inr (Or.inl rfl))).1
  have h4 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((1240 : ℝ) + (j : ℝ)) / 1600) (((1240 : ℝ) + (j : ℝ) + 1) / 1600), u ^
        4 * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((1240 : ℝ) + (j : ℝ) + 1) / 1600) ^ 4 *
        hpThetaJensenCellsBatch062Upper j * ((((1240 : ℝ) + (j : ℝ) + 1) / 1600) - (((1240 : ℝ) +
        (j : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch062_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 4
      (Or.inr (Or.inr rfl))).2
  rw [hs 0 (Or.inl rfl)] at h0
  rw [hs 2 (Or.inr (Or.inl rfl))] at h2
  rw [hs 4 (Or.inr (Or.inr rfl))] at h4
  norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch062Lower,
    hpThetaJensenCellsBatch062Upper] at h0 h2 h4
  norm_num [hpThetaJensenBatchZeroUpper, hpThetaJensenBatchSecondLower,
    hpThetaJensenBatchFourthUpper]
  exact ⟨le_trans h0 (by norm_num), le_trans (by norm_num) h2,
    le_trans h4 (by norm_num)⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Twenty rational terms are verified for each of the three moment orders.
theorem hpThetaJensenCellsBatch063_finiteIntegral_bounds :
    (∫ u : ℝ in Set.Ioo (63 / 80 : ℝ) ((63 + 1) / 80 : ℝ), u ^ 0 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchZeroUpper 63 ∧
    hpThetaJensenBatchSecondLower 63 ≤
        (∫ u : ℝ in Set.Ioo (63 / 80 : ℝ) ((63 + 1) / 80 : ℝ), u ^ 2 *
          hpRiemannThetaDifferentialKernel u) ∧
    (∫ u : ℝ in Set.Ioo (63 / 80 : ℝ) ((63 + 1) / 80 : ℝ), u ^ 4 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchFourthUpper 63 := by
  have hs (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
      (∑ j ∈ Finset.range 20, ∫ u : ℝ in Set.Ioo (((1260 : ℝ) + (j : ℝ)) / 1600) (((1260 : ℝ) + (j
        : ℝ) + 1) / 1600),
        u ^ m * hpRiemannThetaDifferentialKernel u) =
      ∫ u : ℝ in Set.Ioo (63 / 80 : ℝ) ((63 + 1) / 80 : ℝ), u ^ m *
        hpRiemannThetaDifferentialKernel u := by
    have h := hpThetaJensen_batchCellIntegral_sum m hm 63
    have hc : ∀ j : ℕ,
        Set.Ioo (((1260 : ℝ) + (j : ℝ)) / 1600) (((1260 : ℝ) + (j : ℝ) + 1) / 1600) =
          Set.Ioo ((63 : ℝ) / 80 + (j : ℝ) / 1600)
            ((63 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600) := by
      intro j
      have hl : (((1260 : ℝ) + (j : ℝ)) / 1600) = (63 : ℝ) / 80 + (j : ℝ) / 1600 := by ring
      have hr : (((1260 : ℝ) + (j : ℝ) + 1) / 1600) = (63 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600 :=
        by
        push_cast
        ring
      rw [hl, hr]
    simp_rw [hc]
    exact h
  have h0 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((1260 : ℝ) + (j : ℝ)) / 1600) (((1260 : ℝ) + (j : ℝ) + 1) / 1600), u ^
        0 * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((1260 : ℝ) + (j : ℝ) + 1) / 1600) ^ 0 *
        hpThetaJensenCellsBatch063Upper j * ((((1260 : ℝ) + (j : ℝ) + 1) / 1600) - (((1260 : ℝ) +
        (j : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch063_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 0
      (Or.inl rfl)).2
  have h2 : (∑ j ∈ Finset.range 20, (((1260 : ℝ) + (j : ℝ)) / 1600) ^ 2 *
    hpThetaJensenCellsBatch063Lower j * ((((1260 : ℝ) + (j : ℝ) + 1) / 1600) - (((1260 : ℝ) + (j :
    ℝ)) / 1600))) ≤
      ∑ j ∈ Finset.range 20,
        ∫ u : ℝ in Set.Ioo (((1260 : ℝ) + (j : ℝ)) / 1600) (((1260 : ℝ) + (j : ℝ) + 1) / 1600), u
          ^ 2 * hpRiemannThetaDifferentialKernel u := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch063_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 2
      (Or.inr (Or.inl rfl))).1
  have h4 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((1260 : ℝ) + (j : ℝ)) / 1600) (((1260 : ℝ) + (j : ℝ) + 1) / 1600), u ^
        4 * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((1260 : ℝ) + (j : ℝ) + 1) / 1600) ^ 4 *
        hpThetaJensenCellsBatch063Upper j * ((((1260 : ℝ) + (j : ℝ) + 1) / 1600) - (((1260 : ℝ) +
        (j : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch063_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 4
      (Or.inr (Or.inr rfl))).2
  rw [hs 0 (Or.inl rfl)] at h0
  rw [hs 2 (Or.inr (Or.inl rfl))] at h2
  rw [hs 4 (Or.inr (Or.inr rfl))] at h4
  norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch063Lower,
    hpThetaJensenCellsBatch063Upper] at h0 h2 h4
  norm_num [hpThetaJensenBatchZeroUpper, hpThetaJensenBatchSecondLower,
    hpThetaJensenBatchFourthUpper]
  exact ⟨le_trans h0 (by norm_num), le_trans (by norm_num) h2,
    le_trans h4 (by norm_num)⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Twenty rational terms are verified for each of the three moment orders.
theorem hpThetaJensenCellsBatch064_finiteIntegral_bounds :
    (∫ u : ℝ in Set.Ioo (64 / 80 : ℝ) ((64 + 1) / 80 : ℝ), u ^ 0 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchZeroUpper 64 ∧
    hpThetaJensenBatchSecondLower 64 ≤
        (∫ u : ℝ in Set.Ioo (64 / 80 : ℝ) ((64 + 1) / 80 : ℝ), u ^ 2 *
          hpRiemannThetaDifferentialKernel u) ∧
    (∫ u : ℝ in Set.Ioo (64 / 80 : ℝ) ((64 + 1) / 80 : ℝ), u ^ 4 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchFourthUpper 64 := by
  have hs (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
      (∑ j ∈ Finset.range 20, ∫ u : ℝ in Set.Ioo (((1280 : ℝ) + (j : ℝ)) / 1600) (((1280 : ℝ) + (j
        : ℝ) + 1) / 1600),
        u ^ m * hpRiemannThetaDifferentialKernel u) =
      ∫ u : ℝ in Set.Ioo (64 / 80 : ℝ) ((64 + 1) / 80 : ℝ), u ^ m *
        hpRiemannThetaDifferentialKernel u := by
    have h := hpThetaJensen_batchCellIntegral_sum m hm 64
    have hc : ∀ j : ℕ,
        Set.Ioo (((1280 : ℝ) + (j : ℝ)) / 1600) (((1280 : ℝ) + (j : ℝ) + 1) / 1600) =
          Set.Ioo ((64 : ℝ) / 80 + (j : ℝ) / 1600)
            ((64 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600) := by
      intro j
      have hl : (((1280 : ℝ) + (j : ℝ)) / 1600) = (64 : ℝ) / 80 + (j : ℝ) / 1600 := by ring
      have hr : (((1280 : ℝ) + (j : ℝ) + 1) / 1600) = (64 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600 :=
        by
        push_cast
        ring
      rw [hl, hr]
    simp_rw [hc]
    exact h
  have h0 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((1280 : ℝ) + (j : ℝ)) / 1600) (((1280 : ℝ) + (j : ℝ) + 1) / 1600), u ^
        0 * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((1280 : ℝ) + (j : ℝ) + 1) / 1600) ^ 0 *
        hpThetaJensenCellsBatch064Upper j * ((((1280 : ℝ) + (j : ℝ) + 1) / 1600) - (((1280 : ℝ) +
        (j : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch064_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 0
      (Or.inl rfl)).2
  have h2 : (∑ j ∈ Finset.range 20, (((1280 : ℝ) + (j : ℝ)) / 1600) ^ 2 *
    hpThetaJensenCellsBatch064Lower j * ((((1280 : ℝ) + (j : ℝ) + 1) / 1600) - (((1280 : ℝ) + (j :
    ℝ)) / 1600))) ≤
      ∑ j ∈ Finset.range 20,
        ∫ u : ℝ in Set.Ioo (((1280 : ℝ) + (j : ℝ)) / 1600) (((1280 : ℝ) + (j : ℝ) + 1) / 1600), u
          ^ 2 * hpRiemannThetaDifferentialKernel u := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch064_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 2
      (Or.inr (Or.inl rfl))).1
  have h4 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((1280 : ℝ) + (j : ℝ)) / 1600) (((1280 : ℝ) + (j : ℝ) + 1) / 1600), u ^
        4 * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((1280 : ℝ) + (j : ℝ) + 1) / 1600) ^ 4 *
        hpThetaJensenCellsBatch064Upper j * ((((1280 : ℝ) + (j : ℝ) + 1) / 1600) - (((1280 : ℝ) +
        (j : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch064_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 4
      (Or.inr (Or.inr rfl))).2
  rw [hs 0 (Or.inl rfl)] at h0
  rw [hs 2 (Or.inr (Or.inl rfl))] at h2
  rw [hs 4 (Or.inr (Or.inr rfl))] at h4
  norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch064Lower,
    hpThetaJensenCellsBatch064Upper] at h0 h2 h4
  norm_num [hpThetaJensenBatchZeroUpper, hpThetaJensenBatchSecondLower,
    hpThetaJensenBatchFourthUpper]
  exact ⟨le_trans h0 (by norm_num), le_trans (by norm_num) h2,
    le_trans h4 (by norm_num)⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Twenty rational terms are verified for each of the three moment orders.
theorem hpThetaJensenCellsBatch065_finiteIntegral_bounds :
    (∫ u : ℝ in Set.Ioo (65 / 80 : ℝ) ((65 + 1) / 80 : ℝ), u ^ 0 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchZeroUpper 65 ∧
    hpThetaJensenBatchSecondLower 65 ≤
        (∫ u : ℝ in Set.Ioo (65 / 80 : ℝ) ((65 + 1) / 80 : ℝ), u ^ 2 *
          hpRiemannThetaDifferentialKernel u) ∧
    (∫ u : ℝ in Set.Ioo (65 / 80 : ℝ) ((65 + 1) / 80 : ℝ), u ^ 4 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchFourthUpper 65 := by
  have hs (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
      (∑ j ∈ Finset.range 20, ∫ u : ℝ in Set.Ioo (((1300 : ℝ) + (j : ℝ)) / 1600) (((1300 : ℝ) + (j
        : ℝ) + 1) / 1600),
        u ^ m * hpRiemannThetaDifferentialKernel u) =
      ∫ u : ℝ in Set.Ioo (65 / 80 : ℝ) ((65 + 1) / 80 : ℝ), u ^ m *
        hpRiemannThetaDifferentialKernel u := by
    have h := hpThetaJensen_batchCellIntegral_sum m hm 65
    have hc : ∀ j : ℕ,
        Set.Ioo (((1300 : ℝ) + (j : ℝ)) / 1600) (((1300 : ℝ) + (j : ℝ) + 1) / 1600) =
          Set.Ioo ((65 : ℝ) / 80 + (j : ℝ) / 1600)
            ((65 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600) := by
      intro j
      have hl : (((1300 : ℝ) + (j : ℝ)) / 1600) = (65 : ℝ) / 80 + (j : ℝ) / 1600 := by ring
      have hr : (((1300 : ℝ) + (j : ℝ) + 1) / 1600) = (65 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600 :=
        by
        push_cast
        ring
      rw [hl, hr]
    simp_rw [hc]
    exact h
  have h0 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((1300 : ℝ) + (j : ℝ)) / 1600) (((1300 : ℝ) + (j : ℝ) + 1) / 1600), u ^
        0 * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((1300 : ℝ) + (j : ℝ) + 1) / 1600) ^ 0 *
        hpThetaJensenCellsBatch065Upper j * ((((1300 : ℝ) + (j : ℝ) + 1) / 1600) - (((1300 : ℝ) +
        (j : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch065_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 0
      (Or.inl rfl)).2
  have h2 : (∑ j ∈ Finset.range 20, (((1300 : ℝ) + (j : ℝ)) / 1600) ^ 2 *
    hpThetaJensenCellsBatch065Lower j * ((((1300 : ℝ) + (j : ℝ) + 1) / 1600) - (((1300 : ℝ) + (j :
    ℝ)) / 1600))) ≤
      ∑ j ∈ Finset.range 20,
        ∫ u : ℝ in Set.Ioo (((1300 : ℝ) + (j : ℝ)) / 1600) (((1300 : ℝ) + (j : ℝ) + 1) / 1600), u
          ^ 2 * hpRiemannThetaDifferentialKernel u := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch065_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 2
      (Or.inr (Or.inl rfl))).1
  have h4 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((1300 : ℝ) + (j : ℝ)) / 1600) (((1300 : ℝ) + (j : ℝ) + 1) / 1600), u ^
        4 * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((1300 : ℝ) + (j : ℝ) + 1) / 1600) ^ 4 *
        hpThetaJensenCellsBatch065Upper j * ((((1300 : ℝ) + (j : ℝ) + 1) / 1600) - (((1300 : ℝ) +
        (j : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch065_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 4
      (Or.inr (Or.inr rfl))).2
  rw [hs 0 (Or.inl rfl)] at h0
  rw [hs 2 (Or.inr (Or.inl rfl))] at h2
  rw [hs 4 (Or.inr (Or.inr rfl))] at h4
  norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch065Lower,
    hpThetaJensenCellsBatch065Upper] at h0 h2 h4
  norm_num [hpThetaJensenBatchZeroUpper, hpThetaJensenBatchSecondLower,
    hpThetaJensenBatchFourthUpper]
  exact ⟨le_trans h0 (by norm_num), le_trans (by norm_num) h2,
    le_trans h4 (by norm_num)⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Twenty rational terms are verified for each of the three moment orders.
theorem hpThetaJensenCellsBatch066_finiteIntegral_bounds :
    (∫ u : ℝ in Set.Ioo (66 / 80 : ℝ) ((66 + 1) / 80 : ℝ), u ^ 0 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchZeroUpper 66 ∧
    hpThetaJensenBatchSecondLower 66 ≤
        (∫ u : ℝ in Set.Ioo (66 / 80 : ℝ) ((66 + 1) / 80 : ℝ), u ^ 2 *
          hpRiemannThetaDifferentialKernel u) ∧
    (∫ u : ℝ in Set.Ioo (66 / 80 : ℝ) ((66 + 1) / 80 : ℝ), u ^ 4 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchFourthUpper 66 := by
  have hs (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
      (∑ j ∈ Finset.range 20, ∫ u : ℝ in Set.Ioo (((1320 : ℝ) + (j : ℝ)) / 1600) (((1320 : ℝ) + (j
        : ℝ) + 1) / 1600),
        u ^ m * hpRiemannThetaDifferentialKernel u) =
      ∫ u : ℝ in Set.Ioo (66 / 80 : ℝ) ((66 + 1) / 80 : ℝ), u ^ m *
        hpRiemannThetaDifferentialKernel u := by
    have h := hpThetaJensen_batchCellIntegral_sum m hm 66
    have hc : ∀ j : ℕ,
        Set.Ioo (((1320 : ℝ) + (j : ℝ)) / 1600) (((1320 : ℝ) + (j : ℝ) + 1) / 1600) =
          Set.Ioo ((66 : ℝ) / 80 + (j : ℝ) / 1600)
            ((66 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600) := by
      intro j
      have hl : (((1320 : ℝ) + (j : ℝ)) / 1600) = (66 : ℝ) / 80 + (j : ℝ) / 1600 := by ring
      have hr : (((1320 : ℝ) + (j : ℝ) + 1) / 1600) = (66 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600 :=
        by
        push_cast
        ring
      rw [hl, hr]
    simp_rw [hc]
    exact h
  have h0 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((1320 : ℝ) + (j : ℝ)) / 1600) (((1320 : ℝ) + (j : ℝ) + 1) / 1600), u ^
        0 * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((1320 : ℝ) + (j : ℝ) + 1) / 1600) ^ 0 *
        hpThetaJensenCellsBatch066Upper j * ((((1320 : ℝ) + (j : ℝ) + 1) / 1600) - (((1320 : ℝ) +
        (j : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch066_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 0
      (Or.inl rfl)).2
  have h2 : (∑ j ∈ Finset.range 20, (((1320 : ℝ) + (j : ℝ)) / 1600) ^ 2 *
    hpThetaJensenCellsBatch066Lower j * ((((1320 : ℝ) + (j : ℝ) + 1) / 1600) - (((1320 : ℝ) + (j :
    ℝ)) / 1600))) ≤
      ∑ j ∈ Finset.range 20,
        ∫ u : ℝ in Set.Ioo (((1320 : ℝ) + (j : ℝ)) / 1600) (((1320 : ℝ) + (j : ℝ) + 1) / 1600), u
          ^ 2 * hpRiemannThetaDifferentialKernel u := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch066_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 2
      (Or.inr (Or.inl rfl))).1
  have h4 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((1320 : ℝ) + (j : ℝ)) / 1600) (((1320 : ℝ) + (j : ℝ) + 1) / 1600), u ^
        4 * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((1320 : ℝ) + (j : ℝ) + 1) / 1600) ^ 4 *
        hpThetaJensenCellsBatch066Upper j * ((((1320 : ℝ) + (j : ℝ) + 1) / 1600) - (((1320 : ℝ) +
        (j : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch066_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 4
      (Or.inr (Or.inr rfl))).2
  rw [hs 0 (Or.inl rfl)] at h0
  rw [hs 2 (Or.inr (Or.inl rfl))] at h2
  rw [hs 4 (Or.inr (Or.inr rfl))] at h4
  norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch066Lower,
    hpThetaJensenCellsBatch066Upper] at h0 h2 h4
  norm_num [hpThetaJensenBatchZeroUpper, hpThetaJensenBatchSecondLower,
    hpThetaJensenBatchFourthUpper]
  exact ⟨le_trans h0 (by norm_num), le_trans (by norm_num) h2,
    le_trans h4 (by norm_num)⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Twenty rational terms are verified for each of the three moment orders.
theorem hpThetaJensenCellsBatch067_finiteIntegral_bounds :
    (∫ u : ℝ in Set.Ioo (67 / 80 : ℝ) ((67 + 1) / 80 : ℝ), u ^ 0 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchZeroUpper 67 ∧
    hpThetaJensenBatchSecondLower 67 ≤
        (∫ u : ℝ in Set.Ioo (67 / 80 : ℝ) ((67 + 1) / 80 : ℝ), u ^ 2 *
          hpRiemannThetaDifferentialKernel u) ∧
    (∫ u : ℝ in Set.Ioo (67 / 80 : ℝ) ((67 + 1) / 80 : ℝ), u ^ 4 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchFourthUpper 67 := by
  have hs (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
      (∑ j ∈ Finset.range 20, ∫ u : ℝ in Set.Ioo (((1340 : ℝ) + (j : ℝ)) / 1600) (((1340 : ℝ) + (j
        : ℝ) + 1) / 1600),
        u ^ m * hpRiemannThetaDifferentialKernel u) =
      ∫ u : ℝ in Set.Ioo (67 / 80 : ℝ) ((67 + 1) / 80 : ℝ), u ^ m *
        hpRiemannThetaDifferentialKernel u := by
    have h := hpThetaJensen_batchCellIntegral_sum m hm 67
    have hc : ∀ j : ℕ,
        Set.Ioo (((1340 : ℝ) + (j : ℝ)) / 1600) (((1340 : ℝ) + (j : ℝ) + 1) / 1600) =
          Set.Ioo ((67 : ℝ) / 80 + (j : ℝ) / 1600)
            ((67 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600) := by
      intro j
      have hl : (((1340 : ℝ) + (j : ℝ)) / 1600) = (67 : ℝ) / 80 + (j : ℝ) / 1600 := by ring
      have hr : (((1340 : ℝ) + (j : ℝ) + 1) / 1600) = (67 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600 :=
        by
        push_cast
        ring
      rw [hl, hr]
    simp_rw [hc]
    exact h
  have h0 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((1340 : ℝ) + (j : ℝ)) / 1600) (((1340 : ℝ) + (j : ℝ) + 1) / 1600), u ^
        0 * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((1340 : ℝ) + (j : ℝ) + 1) / 1600) ^ 0 *
        hpThetaJensenCellsBatch067Upper j * ((((1340 : ℝ) + (j : ℝ) + 1) / 1600) - (((1340 : ℝ) +
        (j : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch067_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 0
      (Or.inl rfl)).2
  have h2 : (∑ j ∈ Finset.range 20, (((1340 : ℝ) + (j : ℝ)) / 1600) ^ 2 *
    hpThetaJensenCellsBatch067Lower j * ((((1340 : ℝ) + (j : ℝ) + 1) / 1600) - (((1340 : ℝ) + (j :
    ℝ)) / 1600))) ≤
      ∑ j ∈ Finset.range 20,
        ∫ u : ℝ in Set.Ioo (((1340 : ℝ) + (j : ℝ)) / 1600) (((1340 : ℝ) + (j : ℝ) + 1) / 1600), u
          ^ 2 * hpRiemannThetaDifferentialKernel u := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch067_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 2
      (Or.inr (Or.inl rfl))).1
  have h4 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((1340 : ℝ) + (j : ℝ)) / 1600) (((1340 : ℝ) + (j : ℝ) + 1) / 1600), u ^
        4 * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((1340 : ℝ) + (j : ℝ) + 1) / 1600) ^ 4 *
        hpThetaJensenCellsBatch067Upper j * ((((1340 : ℝ) + (j : ℝ) + 1) / 1600) - (((1340 : ℝ) +
        (j : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch067_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 4
      (Or.inr (Or.inr rfl))).2
  rw [hs 0 (Or.inl rfl)] at h0
  rw [hs 2 (Or.inr (Or.inl rfl))] at h2
  rw [hs 4 (Or.inr (Or.inr rfl))] at h4
  norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch067Lower,
    hpThetaJensenCellsBatch067Upper] at h0 h2 h4
  norm_num [hpThetaJensenBatchZeroUpper, hpThetaJensenBatchSecondLower,
    hpThetaJensenBatchFourthUpper]
  exact ⟨le_trans h0 (by norm_num), le_trans (by norm_num) h2,
    le_trans h4 (by norm_num)⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Twenty rational terms are verified for each of the three moment orders.
theorem hpThetaJensenCellsBatch068_finiteIntegral_bounds :
    (∫ u : ℝ in Set.Ioo (68 / 80 : ℝ) ((68 + 1) / 80 : ℝ), u ^ 0 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchZeroUpper 68 ∧
    hpThetaJensenBatchSecondLower 68 ≤
        (∫ u : ℝ in Set.Ioo (68 / 80 : ℝ) ((68 + 1) / 80 : ℝ), u ^ 2 *
          hpRiemannThetaDifferentialKernel u) ∧
    (∫ u : ℝ in Set.Ioo (68 / 80 : ℝ) ((68 + 1) / 80 : ℝ), u ^ 4 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchFourthUpper 68 := by
  have hs (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
      (∑ j ∈ Finset.range 20, ∫ u : ℝ in Set.Ioo (((1360 : ℝ) + (j : ℝ)) / 1600) (((1360 : ℝ) + (j
        : ℝ) + 1) / 1600),
        u ^ m * hpRiemannThetaDifferentialKernel u) =
      ∫ u : ℝ in Set.Ioo (68 / 80 : ℝ) ((68 + 1) / 80 : ℝ), u ^ m *
        hpRiemannThetaDifferentialKernel u := by
    have h := hpThetaJensen_batchCellIntegral_sum m hm 68
    have hc : ∀ j : ℕ,
        Set.Ioo (((1360 : ℝ) + (j : ℝ)) / 1600) (((1360 : ℝ) + (j : ℝ) + 1) / 1600) =
          Set.Ioo ((68 : ℝ) / 80 + (j : ℝ) / 1600)
            ((68 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600) := by
      intro j
      have hl : (((1360 : ℝ) + (j : ℝ)) / 1600) = (68 : ℝ) / 80 + (j : ℝ) / 1600 := by ring
      have hr : (((1360 : ℝ) + (j : ℝ) + 1) / 1600) = (68 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600 :=
        by
        push_cast
        ring
      rw [hl, hr]
    simp_rw [hc]
    exact h
  have h0 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((1360 : ℝ) + (j : ℝ)) / 1600) (((1360 : ℝ) + (j : ℝ) + 1) / 1600), u ^
        0 * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((1360 : ℝ) + (j : ℝ) + 1) / 1600) ^ 0 *
        hpThetaJensenCellsBatch068Upper j * ((((1360 : ℝ) + (j : ℝ) + 1) / 1600) - (((1360 : ℝ) +
        (j : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch068_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 0
      (Or.inl rfl)).2
  have h2 : (∑ j ∈ Finset.range 20, (((1360 : ℝ) + (j : ℝ)) / 1600) ^ 2 *
    hpThetaJensenCellsBatch068Lower j * ((((1360 : ℝ) + (j : ℝ) + 1) / 1600) - (((1360 : ℝ) + (j :
    ℝ)) / 1600))) ≤
      ∑ j ∈ Finset.range 20,
        ∫ u : ℝ in Set.Ioo (((1360 : ℝ) + (j : ℝ)) / 1600) (((1360 : ℝ) + (j : ℝ) + 1) / 1600), u
          ^ 2 * hpRiemannThetaDifferentialKernel u := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch068_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 2
      (Or.inr (Or.inl rfl))).1
  have h4 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((1360 : ℝ) + (j : ℝ)) / 1600) (((1360 : ℝ) + (j : ℝ) + 1) / 1600), u ^
        4 * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((1360 : ℝ) + (j : ℝ) + 1) / 1600) ^ 4 *
        hpThetaJensenCellsBatch068Upper j * ((((1360 : ℝ) + (j : ℝ) + 1) / 1600) - (((1360 : ℝ) +
        (j : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch068_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 4
      (Or.inr (Or.inr rfl))).2
  rw [hs 0 (Or.inl rfl)] at h0
  rw [hs 2 (Or.inr (Or.inl rfl))] at h2
  rw [hs 4 (Or.inr (Or.inr rfl))] at h4
  norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch068Lower,
    hpThetaJensenCellsBatch068Upper] at h0 h2 h4
  norm_num [hpThetaJensenBatchZeroUpper, hpThetaJensenBatchSecondLower,
    hpThetaJensenBatchFourthUpper]
  exact ⟨le_trans h0 (by norm_num), le_trans (by norm_num) h2,
    le_trans h4 (by norm_num)⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Twenty rational terms are verified for each of the three moment orders.
theorem hpThetaJensenCellsBatch069_finiteIntegral_bounds :
    (∫ u : ℝ in Set.Ioo (69 / 80 : ℝ) ((69 + 1) / 80 : ℝ), u ^ 0 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchZeroUpper 69 ∧
    hpThetaJensenBatchSecondLower 69 ≤
        (∫ u : ℝ in Set.Ioo (69 / 80 : ℝ) ((69 + 1) / 80 : ℝ), u ^ 2 *
          hpRiemannThetaDifferentialKernel u) ∧
    (∫ u : ℝ in Set.Ioo (69 / 80 : ℝ) ((69 + 1) / 80 : ℝ), u ^ 4 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchFourthUpper 69 := by
  have hs (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
      (∑ j ∈ Finset.range 20, ∫ u : ℝ in Set.Ioo (((1380 : ℝ) + (j : ℝ)) / 1600) (((1380 : ℝ) + (j
        : ℝ) + 1) / 1600),
        u ^ m * hpRiemannThetaDifferentialKernel u) =
      ∫ u : ℝ in Set.Ioo (69 / 80 : ℝ) ((69 + 1) / 80 : ℝ), u ^ m *
        hpRiemannThetaDifferentialKernel u := by
    have h := hpThetaJensen_batchCellIntegral_sum m hm 69
    have hc : ∀ j : ℕ,
        Set.Ioo (((1380 : ℝ) + (j : ℝ)) / 1600) (((1380 : ℝ) + (j : ℝ) + 1) / 1600) =
          Set.Ioo ((69 : ℝ) / 80 + (j : ℝ) / 1600)
            ((69 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600) := by
      intro j
      have hl : (((1380 : ℝ) + (j : ℝ)) / 1600) = (69 : ℝ) / 80 + (j : ℝ) / 1600 := by ring
      have hr : (((1380 : ℝ) + (j : ℝ) + 1) / 1600) = (69 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600 :=
        by
        push_cast
        ring
      rw [hl, hr]
    simp_rw [hc]
    exact h
  have h0 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((1380 : ℝ) + (j : ℝ)) / 1600) (((1380 : ℝ) + (j : ℝ) + 1) / 1600), u ^
        0 * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((1380 : ℝ) + (j : ℝ) + 1) / 1600) ^ 0 *
        hpThetaJensenCellsBatch069Upper j * ((((1380 : ℝ) + (j : ℝ) + 1) / 1600) - (((1380 : ℝ) +
        (j : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch069_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 0
      (Or.inl rfl)).2
  have h2 : (∑ j ∈ Finset.range 20, (((1380 : ℝ) + (j : ℝ)) / 1600) ^ 2 *
    hpThetaJensenCellsBatch069Lower j * ((((1380 : ℝ) + (j : ℝ) + 1) / 1600) - (((1380 : ℝ) + (j :
    ℝ)) / 1600))) ≤
      ∑ j ∈ Finset.range 20,
        ∫ u : ℝ in Set.Ioo (((1380 : ℝ) + (j : ℝ)) / 1600) (((1380 : ℝ) + (j : ℝ) + 1) / 1600), u
          ^ 2 * hpRiemannThetaDifferentialKernel u := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch069_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 2
      (Or.inr (Or.inl rfl))).1
  have h4 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((1380 : ℝ) + (j : ℝ)) / 1600) (((1380 : ℝ) + (j : ℝ) + 1) / 1600), u ^
        4 * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((1380 : ℝ) + (j : ℝ) + 1) / 1600) ^ 4 *
        hpThetaJensenCellsBatch069Upper j * ((((1380 : ℝ) + (j : ℝ) + 1) / 1600) - (((1380 : ℝ) +
        (j : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch069_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 4
      (Or.inr (Or.inr rfl))).2
  rw [hs 0 (Or.inl rfl)] at h0
  rw [hs 2 (Or.inr (Or.inl rfl))] at h2
  rw [hs 4 (Or.inr (Or.inr rfl))] at h4
  norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch069Lower,
    hpThetaJensenCellsBatch069Upper] at h0 h2 h4
  norm_num [hpThetaJensenBatchZeroUpper, hpThetaJensenBatchSecondLower,
    hpThetaJensenBatchFourthUpper]
  exact ⟨le_trans h0 (by norm_num), le_trans (by norm_num) h2,
    le_trans h4 (by norm_num)⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Twenty rational terms are verified for each of the three moment orders.
theorem hpThetaJensenCellsBatch070_finiteIntegral_bounds :
    (∫ u : ℝ in Set.Ioo (70 / 80 : ℝ) ((70 + 1) / 80 : ℝ), u ^ 0 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchZeroUpper 70 ∧
    hpThetaJensenBatchSecondLower 70 ≤
        (∫ u : ℝ in Set.Ioo (70 / 80 : ℝ) ((70 + 1) / 80 : ℝ), u ^ 2 *
          hpRiemannThetaDifferentialKernel u) ∧
    (∫ u : ℝ in Set.Ioo (70 / 80 : ℝ) ((70 + 1) / 80 : ℝ), u ^ 4 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchFourthUpper 70 := by
  have hs (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
      (∑ j ∈ Finset.range 20, ∫ u : ℝ in Set.Ioo (((1400 : ℝ) + (j : ℝ)) / 1600) (((1400 : ℝ) + (j
        : ℝ) + 1) / 1600),
        u ^ m * hpRiemannThetaDifferentialKernel u) =
      ∫ u : ℝ in Set.Ioo (70 / 80 : ℝ) ((70 + 1) / 80 : ℝ), u ^ m *
        hpRiemannThetaDifferentialKernel u := by
    have h := hpThetaJensen_batchCellIntegral_sum m hm 70
    have hc : ∀ j : ℕ,
        Set.Ioo (((1400 : ℝ) + (j : ℝ)) / 1600) (((1400 : ℝ) + (j : ℝ) + 1) / 1600) =
          Set.Ioo ((70 : ℝ) / 80 + (j : ℝ) / 1600)
            ((70 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600) := by
      intro j
      have hl : (((1400 : ℝ) + (j : ℝ)) / 1600) = (70 : ℝ) / 80 + (j : ℝ) / 1600 := by ring
      have hr : (((1400 : ℝ) + (j : ℝ) + 1) / 1600) = (70 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600 :=
        by
        push_cast
        ring
      rw [hl, hr]
    simp_rw [hc]
    exact h
  have h0 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((1400 : ℝ) + (j : ℝ)) / 1600) (((1400 : ℝ) + (j : ℝ) + 1) / 1600), u ^
        0 * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((1400 : ℝ) + (j : ℝ) + 1) / 1600) ^ 0 *
        hpThetaJensenCellsBatch070Upper j * ((((1400 : ℝ) + (j : ℝ) + 1) / 1600) - (((1400 : ℝ) +
        (j : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch070_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 0
      (Or.inl rfl)).2
  have h2 : (∑ j ∈ Finset.range 20, (((1400 : ℝ) + (j : ℝ)) / 1600) ^ 2 *
    hpThetaJensenCellsBatch070Lower j * ((((1400 : ℝ) + (j : ℝ) + 1) / 1600) - (((1400 : ℝ) + (j :
    ℝ)) / 1600))) ≤
      ∑ j ∈ Finset.range 20,
        ∫ u : ℝ in Set.Ioo (((1400 : ℝ) + (j : ℝ)) / 1600) (((1400 : ℝ) + (j : ℝ) + 1) / 1600), u
          ^ 2 * hpRiemannThetaDifferentialKernel u := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch070_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 2
      (Or.inr (Or.inl rfl))).1
  have h4 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((1400 : ℝ) + (j : ℝ)) / 1600) (((1400 : ℝ) + (j : ℝ) + 1) / 1600), u ^
        4 * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((1400 : ℝ) + (j : ℝ) + 1) / 1600) ^ 4 *
        hpThetaJensenCellsBatch070Upper j * ((((1400 : ℝ) + (j : ℝ) + 1) / 1600) - (((1400 : ℝ) +
        (j : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch070_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 4
      (Or.inr (Or.inr rfl))).2
  rw [hs 0 (Or.inl rfl)] at h0
  rw [hs 2 (Or.inr (Or.inl rfl))] at h2
  rw [hs 4 (Or.inr (Or.inr rfl))] at h4
  norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch070Lower,
    hpThetaJensenCellsBatch070Upper] at h0 h2 h4
  norm_num [hpThetaJensenBatchZeroUpper, hpThetaJensenBatchSecondLower,
    hpThetaJensenBatchFourthUpper]
  exact ⟨le_trans h0 (by norm_num), le_trans (by norm_num) h2,
    le_trans h4 (by norm_num)⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Twenty rational terms are verified for each of the three moment orders.
theorem hpThetaJensenCellsBatch071_finiteIntegral_bounds :
    (∫ u : ℝ in Set.Ioo (71 / 80 : ℝ) ((71 + 1) / 80 : ℝ), u ^ 0 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchZeroUpper 71 ∧
    hpThetaJensenBatchSecondLower 71 ≤
        (∫ u : ℝ in Set.Ioo (71 / 80 : ℝ) ((71 + 1) / 80 : ℝ), u ^ 2 *
          hpRiemannThetaDifferentialKernel u) ∧
    (∫ u : ℝ in Set.Ioo (71 / 80 : ℝ) ((71 + 1) / 80 : ℝ), u ^ 4 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchFourthUpper 71 := by
  have hs (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
      (∑ j ∈ Finset.range 20, ∫ u : ℝ in Set.Ioo (((1420 : ℝ) + (j : ℝ)) / 1600) (((1420 : ℝ) + (j
        : ℝ) + 1) / 1600),
        u ^ m * hpRiemannThetaDifferentialKernel u) =
      ∫ u : ℝ in Set.Ioo (71 / 80 : ℝ) ((71 + 1) / 80 : ℝ), u ^ m *
        hpRiemannThetaDifferentialKernel u := by
    have h := hpThetaJensen_batchCellIntegral_sum m hm 71
    have hc : ∀ j : ℕ,
        Set.Ioo (((1420 : ℝ) + (j : ℝ)) / 1600) (((1420 : ℝ) + (j : ℝ) + 1) / 1600) =
          Set.Ioo ((71 : ℝ) / 80 + (j : ℝ) / 1600)
            ((71 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600) := by
      intro j
      have hl : (((1420 : ℝ) + (j : ℝ)) / 1600) = (71 : ℝ) / 80 + (j : ℝ) / 1600 := by ring
      have hr : (((1420 : ℝ) + (j : ℝ) + 1) / 1600) = (71 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600 :=
        by
        push_cast
        ring
      rw [hl, hr]
    simp_rw [hc]
    exact h
  have h0 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((1420 : ℝ) + (j : ℝ)) / 1600) (((1420 : ℝ) + (j : ℝ) + 1) / 1600), u ^
        0 * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((1420 : ℝ) + (j : ℝ) + 1) / 1600) ^ 0 *
        hpThetaJensenCellsBatch071Upper j * ((((1420 : ℝ) + (j : ℝ) + 1) / 1600) - (((1420 : ℝ) +
        (j : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch071_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 0
      (Or.inl rfl)).2
  have h2 : (∑ j ∈ Finset.range 20, (((1420 : ℝ) + (j : ℝ)) / 1600) ^ 2 *
    hpThetaJensenCellsBatch071Lower j * ((((1420 : ℝ) + (j : ℝ) + 1) / 1600) - (((1420 : ℝ) + (j :
    ℝ)) / 1600))) ≤
      ∑ j ∈ Finset.range 20,
        ∫ u : ℝ in Set.Ioo (((1420 : ℝ) + (j : ℝ)) / 1600) (((1420 : ℝ) + (j : ℝ) + 1) / 1600), u
          ^ 2 * hpRiemannThetaDifferentialKernel u := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch071_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 2
      (Or.inr (Or.inl rfl))).1
  have h4 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((1420 : ℝ) + (j : ℝ)) / 1600) (((1420 : ℝ) + (j : ℝ) + 1) / 1600), u ^
        4 * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((1420 : ℝ) + (j : ℝ) + 1) / 1600) ^ 4 *
        hpThetaJensenCellsBatch071Upper j * ((((1420 : ℝ) + (j : ℝ) + 1) / 1600) - (((1420 : ℝ) +
        (j : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch071_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 4
      (Or.inr (Or.inr rfl))).2
  rw [hs 0 (Or.inl rfl)] at h0
  rw [hs 2 (Or.inr (Or.inl rfl))] at h2
  rw [hs 4 (Or.inr (Or.inr rfl))] at h4
  norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch071Lower,
    hpThetaJensenCellsBatch071Upper] at h0 h2 h4
  norm_num [hpThetaJensenBatchZeroUpper, hpThetaJensenBatchSecondLower,
    hpThetaJensenBatchFourthUpper]
  exact ⟨le_trans h0 (by norm_num), le_trans (by norm_num) h2,
    le_trans h4 (by norm_num)⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Twenty rational terms are verified for each of the three moment orders.
theorem hpThetaJensenCellsBatch072_finiteIntegral_bounds :
    (∫ u : ℝ in Set.Ioo (72 / 80 : ℝ) ((72 + 1) / 80 : ℝ), u ^ 0 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchZeroUpper 72 ∧
    hpThetaJensenBatchSecondLower 72 ≤
        (∫ u : ℝ in Set.Ioo (72 / 80 : ℝ) ((72 + 1) / 80 : ℝ), u ^ 2 *
          hpRiemannThetaDifferentialKernel u) ∧
    (∫ u : ℝ in Set.Ioo (72 / 80 : ℝ) ((72 + 1) / 80 : ℝ), u ^ 4 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchFourthUpper 72 := by
  have hs (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
      (∑ j ∈ Finset.range 20, ∫ u : ℝ in Set.Ioo (((1440 : ℝ) + (j : ℝ)) / 1600) (((1440 : ℝ) + (j
        : ℝ) + 1) / 1600),
        u ^ m * hpRiemannThetaDifferentialKernel u) =
      ∫ u : ℝ in Set.Ioo (72 / 80 : ℝ) ((72 + 1) / 80 : ℝ), u ^ m *
        hpRiemannThetaDifferentialKernel u := by
    have h := hpThetaJensen_batchCellIntegral_sum m hm 72
    have hc : ∀ j : ℕ,
        Set.Ioo (((1440 : ℝ) + (j : ℝ)) / 1600) (((1440 : ℝ) + (j : ℝ) + 1) / 1600) =
          Set.Ioo ((72 : ℝ) / 80 + (j : ℝ) / 1600)
            ((72 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600) := by
      intro j
      have hl : (((1440 : ℝ) + (j : ℝ)) / 1600) = (72 : ℝ) / 80 + (j : ℝ) / 1600 := by ring
      have hr : (((1440 : ℝ) + (j : ℝ) + 1) / 1600) = (72 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600 :=
        by
        push_cast
        ring
      rw [hl, hr]
    simp_rw [hc]
    exact h
  have h0 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((1440 : ℝ) + (j : ℝ)) / 1600) (((1440 : ℝ) + (j : ℝ) + 1) / 1600), u ^
        0 * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((1440 : ℝ) + (j : ℝ) + 1) / 1600) ^ 0 *
        hpThetaJensenCellsBatch072Upper j * ((((1440 : ℝ) + (j : ℝ) + 1) / 1600) - (((1440 : ℝ) +
        (j : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch072_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 0
      (Or.inl rfl)).2
  have h2 : (∑ j ∈ Finset.range 20, (((1440 : ℝ) + (j : ℝ)) / 1600) ^ 2 *
    hpThetaJensenCellsBatch072Lower j * ((((1440 : ℝ) + (j : ℝ) + 1) / 1600) - (((1440 : ℝ) + (j :
    ℝ)) / 1600))) ≤
      ∑ j ∈ Finset.range 20,
        ∫ u : ℝ in Set.Ioo (((1440 : ℝ) + (j : ℝ)) / 1600) (((1440 : ℝ) + (j : ℝ) + 1) / 1600), u
          ^ 2 * hpRiemannThetaDifferentialKernel u := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch072_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 2
      (Or.inr (Or.inl rfl))).1
  have h4 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((1440 : ℝ) + (j : ℝ)) / 1600) (((1440 : ℝ) + (j : ℝ) + 1) / 1600), u ^
        4 * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((1440 : ℝ) + (j : ℝ) + 1) / 1600) ^ 4 *
        hpThetaJensenCellsBatch072Upper j * ((((1440 : ℝ) + (j : ℝ) + 1) / 1600) - (((1440 : ℝ) +
        (j : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch072_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 4
      (Or.inr (Or.inr rfl))).2
  rw [hs 0 (Or.inl rfl)] at h0
  rw [hs 2 (Or.inr (Or.inl rfl))] at h2
  rw [hs 4 (Or.inr (Or.inr rfl))] at h4
  norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch072Lower,
    hpThetaJensenCellsBatch072Upper] at h0 h2 h4
  norm_num [hpThetaJensenBatchZeroUpper, hpThetaJensenBatchSecondLower,
    hpThetaJensenBatchFourthUpper]
  exact ⟨le_trans h0 (by norm_num), le_trans (by norm_num) h2,
    le_trans h4 (by norm_num)⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Twenty rational terms are verified for each of the three moment orders.
theorem hpThetaJensenCellsBatch073_finiteIntegral_bounds :
    (∫ u : ℝ in Set.Ioo (73 / 80 : ℝ) ((73 + 1) / 80 : ℝ), u ^ 0 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchZeroUpper 73 ∧
    hpThetaJensenBatchSecondLower 73 ≤
        (∫ u : ℝ in Set.Ioo (73 / 80 : ℝ) ((73 + 1) / 80 : ℝ), u ^ 2 *
          hpRiemannThetaDifferentialKernel u) ∧
    (∫ u : ℝ in Set.Ioo (73 / 80 : ℝ) ((73 + 1) / 80 : ℝ), u ^ 4 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchFourthUpper 73 := by
  have hs (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
      (∑ j ∈ Finset.range 20, ∫ u : ℝ in Set.Ioo (((1460 : ℝ) + (j : ℝ)) / 1600) (((1460 : ℝ) + (j
        : ℝ) + 1) / 1600),
        u ^ m * hpRiemannThetaDifferentialKernel u) =
      ∫ u : ℝ in Set.Ioo (73 / 80 : ℝ) ((73 + 1) / 80 : ℝ), u ^ m *
        hpRiemannThetaDifferentialKernel u := by
    have h := hpThetaJensen_batchCellIntegral_sum m hm 73
    have hc : ∀ j : ℕ,
        Set.Ioo (((1460 : ℝ) + (j : ℝ)) / 1600) (((1460 : ℝ) + (j : ℝ) + 1) / 1600) =
          Set.Ioo ((73 : ℝ) / 80 + (j : ℝ) / 1600)
            ((73 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600) := by
      intro j
      have hl : (((1460 : ℝ) + (j : ℝ)) / 1600) = (73 : ℝ) / 80 + (j : ℝ) / 1600 := by ring
      have hr : (((1460 : ℝ) + (j : ℝ) + 1) / 1600) = (73 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600 :=
        by
        push_cast
        ring
      rw [hl, hr]
    simp_rw [hc]
    exact h
  have h0 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((1460 : ℝ) + (j : ℝ)) / 1600) (((1460 : ℝ) + (j : ℝ) + 1) / 1600), u ^
        0 * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((1460 : ℝ) + (j : ℝ) + 1) / 1600) ^ 0 *
        hpThetaJensenCellsBatch073Upper j * ((((1460 : ℝ) + (j : ℝ) + 1) / 1600) - (((1460 : ℝ) +
        (j : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch073_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 0
      (Or.inl rfl)).2
  have h2 : (∑ j ∈ Finset.range 20, (((1460 : ℝ) + (j : ℝ)) / 1600) ^ 2 *
    hpThetaJensenCellsBatch073Lower j * ((((1460 : ℝ) + (j : ℝ) + 1) / 1600) - (((1460 : ℝ) + (j :
    ℝ)) / 1600))) ≤
      ∑ j ∈ Finset.range 20,
        ∫ u : ℝ in Set.Ioo (((1460 : ℝ) + (j : ℝ)) / 1600) (((1460 : ℝ) + (j : ℝ) + 1) / 1600), u
          ^ 2 * hpRiemannThetaDifferentialKernel u := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch073_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 2
      (Or.inr (Or.inl rfl))).1
  have h4 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((1460 : ℝ) + (j : ℝ)) / 1600) (((1460 : ℝ) + (j : ℝ) + 1) / 1600), u ^
        4 * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((1460 : ℝ) + (j : ℝ) + 1) / 1600) ^ 4 *
        hpThetaJensenCellsBatch073Upper j * ((((1460 : ℝ) + (j : ℝ) + 1) / 1600) - (((1460 : ℝ) +
        (j : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch073_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 4
      (Or.inr (Or.inr rfl))).2
  rw [hs 0 (Or.inl rfl)] at h0
  rw [hs 2 (Or.inr (Or.inl rfl))] at h2
  rw [hs 4 (Or.inr (Or.inr rfl))] at h4
  norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch073Lower,
    hpThetaJensenCellsBatch073Upper] at h0 h2 h4
  norm_num [hpThetaJensenBatchZeroUpper, hpThetaJensenBatchSecondLower,
    hpThetaJensenBatchFourthUpper]
  exact ⟨le_trans h0 (by norm_num), le_trans (by norm_num) h2,
    le_trans h4 (by norm_num)⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Twenty rational terms are verified for each of the three moment orders.
theorem hpThetaJensenCellsBatch074_finiteIntegral_bounds :
    (∫ u : ℝ in Set.Ioo (74 / 80 : ℝ) ((74 + 1) / 80 : ℝ), u ^ 0 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchZeroUpper 74 ∧
    hpThetaJensenBatchSecondLower 74 ≤
        (∫ u : ℝ in Set.Ioo (74 / 80 : ℝ) ((74 + 1) / 80 : ℝ), u ^ 2 *
          hpRiemannThetaDifferentialKernel u) ∧
    (∫ u : ℝ in Set.Ioo (74 / 80 : ℝ) ((74 + 1) / 80 : ℝ), u ^ 4 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchFourthUpper 74 := by
  have hs (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
      (∑ j ∈ Finset.range 20, ∫ u : ℝ in Set.Ioo (((1480 : ℝ) + (j : ℝ)) / 1600) (((1480 : ℝ) + (j
        : ℝ) + 1) / 1600),
        u ^ m * hpRiemannThetaDifferentialKernel u) =
      ∫ u : ℝ in Set.Ioo (74 / 80 : ℝ) ((74 + 1) / 80 : ℝ), u ^ m *
        hpRiemannThetaDifferentialKernel u := by
    have h := hpThetaJensen_batchCellIntegral_sum m hm 74
    have hc : ∀ j : ℕ,
        Set.Ioo (((1480 : ℝ) + (j : ℝ)) / 1600) (((1480 : ℝ) + (j : ℝ) + 1) / 1600) =
          Set.Ioo ((74 : ℝ) / 80 + (j : ℝ) / 1600)
            ((74 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600) := by
      intro j
      have hl : (((1480 : ℝ) + (j : ℝ)) / 1600) = (74 : ℝ) / 80 + (j : ℝ) / 1600 := by ring
      have hr : (((1480 : ℝ) + (j : ℝ) + 1) / 1600) = (74 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600 :=
        by
        push_cast
        ring
      rw [hl, hr]
    simp_rw [hc]
    exact h
  have h0 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((1480 : ℝ) + (j : ℝ)) / 1600) (((1480 : ℝ) + (j : ℝ) + 1) / 1600), u ^
        0 * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((1480 : ℝ) + (j : ℝ) + 1) / 1600) ^ 0 *
        hpThetaJensenCellsBatch074Upper j * ((((1480 : ℝ) + (j : ℝ) + 1) / 1600) - (((1480 : ℝ) +
        (j : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch074_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 0
      (Or.inl rfl)).2
  have h2 : (∑ j ∈ Finset.range 20, (((1480 : ℝ) + (j : ℝ)) / 1600) ^ 2 *
    hpThetaJensenCellsBatch074Lower j * ((((1480 : ℝ) + (j : ℝ) + 1) / 1600) - (((1480 : ℝ) + (j :
    ℝ)) / 1600))) ≤
      ∑ j ∈ Finset.range 20,
        ∫ u : ℝ in Set.Ioo (((1480 : ℝ) + (j : ℝ)) / 1600) (((1480 : ℝ) + (j : ℝ) + 1) / 1600), u
          ^ 2 * hpRiemannThetaDifferentialKernel u := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch074_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 2
      (Or.inr (Or.inl rfl))).1
  have h4 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((1480 : ℝ) + (j : ℝ)) / 1600) (((1480 : ℝ) + (j : ℝ) + 1) / 1600), u ^
        4 * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((1480 : ℝ) + (j : ℝ) + 1) / 1600) ^ 4 *
        hpThetaJensenCellsBatch074Upper j * ((((1480 : ℝ) + (j : ℝ) + 1) / 1600) - (((1480 : ℝ) +
        (j : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch074_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 4
      (Or.inr (Or.inr rfl))).2
  rw [hs 0 (Or.inl rfl)] at h0
  rw [hs 2 (Or.inr (Or.inl rfl))] at h2
  rw [hs 4 (Or.inr (Or.inr rfl))] at h4
  norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch074Lower,
    hpThetaJensenCellsBatch074Upper] at h0 h2 h4
  norm_num [hpThetaJensenBatchZeroUpper, hpThetaJensenBatchSecondLower,
    hpThetaJensenBatchFourthUpper]
  exact ⟨le_trans h0 (by norm_num), le_trans (by norm_num) h2,
    le_trans h4 (by norm_num)⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Twenty rational terms are verified for each of the three moment orders.
theorem hpThetaJensenCellsBatch075_finiteIntegral_bounds :
    (∫ u : ℝ in Set.Ioo (75 / 80 : ℝ) ((75 + 1) / 80 : ℝ), u ^ 0 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchZeroUpper 75 ∧
    hpThetaJensenBatchSecondLower 75 ≤
        (∫ u : ℝ in Set.Ioo (75 / 80 : ℝ) ((75 + 1) / 80 : ℝ), u ^ 2 *
          hpRiemannThetaDifferentialKernel u) ∧
    (∫ u : ℝ in Set.Ioo (75 / 80 : ℝ) ((75 + 1) / 80 : ℝ), u ^ 4 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchFourthUpper 75 := by
  have hs (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
      (∑ j ∈ Finset.range 20, ∫ u : ℝ in Set.Ioo (((1500 : ℝ) + (j : ℝ)) / 1600) (((1500 : ℝ) + (j
        : ℝ) + 1) / 1600),
        u ^ m * hpRiemannThetaDifferentialKernel u) =
      ∫ u : ℝ in Set.Ioo (75 / 80 : ℝ) ((75 + 1) / 80 : ℝ), u ^ m *
        hpRiemannThetaDifferentialKernel u := by
    have h := hpThetaJensen_batchCellIntegral_sum m hm 75
    have hc : ∀ j : ℕ,
        Set.Ioo (((1500 : ℝ) + (j : ℝ)) / 1600) (((1500 : ℝ) + (j : ℝ) + 1) / 1600) =
          Set.Ioo ((75 : ℝ) / 80 + (j : ℝ) / 1600)
            ((75 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600) := by
      intro j
      have hl : (((1500 : ℝ) + (j : ℝ)) / 1600) = (75 : ℝ) / 80 + (j : ℝ) / 1600 := by ring
      have hr : (((1500 : ℝ) + (j : ℝ) + 1) / 1600) = (75 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600 :=
        by
        push_cast
        ring
      rw [hl, hr]
    simp_rw [hc]
    exact h
  have h0 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((1500 : ℝ) + (j : ℝ)) / 1600) (((1500 : ℝ) + (j : ℝ) + 1) / 1600), u ^
        0 * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((1500 : ℝ) + (j : ℝ) + 1) / 1600) ^ 0 *
        hpThetaJensenCellsBatch075Upper j * ((((1500 : ℝ) + (j : ℝ) + 1) / 1600) - (((1500 : ℝ) +
        (j : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch075_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 0
      (Or.inl rfl)).2
  have h2 : (∑ j ∈ Finset.range 20, (((1500 : ℝ) + (j : ℝ)) / 1600) ^ 2 *
    hpThetaJensenCellsBatch075Lower j * ((((1500 : ℝ) + (j : ℝ) + 1) / 1600) - (((1500 : ℝ) + (j :
    ℝ)) / 1600))) ≤
      ∑ j ∈ Finset.range 20,
        ∫ u : ℝ in Set.Ioo (((1500 : ℝ) + (j : ℝ)) / 1600) (((1500 : ℝ) + (j : ℝ) + 1) / 1600), u
          ^ 2 * hpRiemannThetaDifferentialKernel u := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch075_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 2
      (Or.inr (Or.inl rfl))).1
  have h4 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((1500 : ℝ) + (j : ℝ)) / 1600) (((1500 : ℝ) + (j : ℝ) + 1) / 1600), u ^
        4 * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((1500 : ℝ) + (j : ℝ) + 1) / 1600) ^ 4 *
        hpThetaJensenCellsBatch075Upper j * ((((1500 : ℝ) + (j : ℝ) + 1) / 1600) - (((1500 : ℝ) +
        (j : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch075_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 4
      (Or.inr (Or.inr rfl))).2
  rw [hs 0 (Or.inl rfl)] at h0
  rw [hs 2 (Or.inr (Or.inl rfl))] at h2
  rw [hs 4 (Or.inr (Or.inr rfl))] at h4
  norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch075Lower,
    hpThetaJensenCellsBatch075Upper] at h0 h2 h4
  norm_num [hpThetaJensenBatchZeroUpper, hpThetaJensenBatchSecondLower,
    hpThetaJensenBatchFourthUpper]
  exact ⟨le_trans h0 (by norm_num), le_trans (by norm_num) h2,
    le_trans h4 (by norm_num)⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Twenty rational terms are verified for each of the three moment orders.
theorem hpThetaJensenCellsBatch076_finiteIntegral_bounds :
    (∫ u : ℝ in Set.Ioo (76 / 80 : ℝ) ((76 + 1) / 80 : ℝ), u ^ 0 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchZeroUpper 76 ∧
    hpThetaJensenBatchSecondLower 76 ≤
        (∫ u : ℝ in Set.Ioo (76 / 80 : ℝ) ((76 + 1) / 80 : ℝ), u ^ 2 *
          hpRiemannThetaDifferentialKernel u) ∧
    (∫ u : ℝ in Set.Ioo (76 / 80 : ℝ) ((76 + 1) / 80 : ℝ), u ^ 4 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchFourthUpper 76 := by
  have hs (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
      (∑ j ∈ Finset.range 20, ∫ u : ℝ in Set.Ioo (((1520 : ℝ) + (j : ℝ)) / 1600) (((1520 : ℝ) + (j
        : ℝ) + 1) / 1600),
        u ^ m * hpRiemannThetaDifferentialKernel u) =
      ∫ u : ℝ in Set.Ioo (76 / 80 : ℝ) ((76 + 1) / 80 : ℝ), u ^ m *
        hpRiemannThetaDifferentialKernel u := by
    have h := hpThetaJensen_batchCellIntegral_sum m hm 76
    have hc : ∀ j : ℕ,
        Set.Ioo (((1520 : ℝ) + (j : ℝ)) / 1600) (((1520 : ℝ) + (j : ℝ) + 1) / 1600) =
          Set.Ioo ((76 : ℝ) / 80 + (j : ℝ) / 1600)
            ((76 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600) := by
      intro j
      have hl : (((1520 : ℝ) + (j : ℝ)) / 1600) = (76 : ℝ) / 80 + (j : ℝ) / 1600 := by ring
      have hr : (((1520 : ℝ) + (j : ℝ) + 1) / 1600) = (76 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600 :=
        by
        push_cast
        ring
      rw [hl, hr]
    simp_rw [hc]
    exact h
  have h0 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((1520 : ℝ) + (j : ℝ)) / 1600) (((1520 : ℝ) + (j : ℝ) + 1) / 1600), u ^
        0 * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((1520 : ℝ) + (j : ℝ) + 1) / 1600) ^ 0 *
        hpThetaJensenCellsBatch076Upper j * ((((1520 : ℝ) + (j : ℝ) + 1) / 1600) - (((1520 : ℝ) +
        (j : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch076_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 0
      (Or.inl rfl)).2
  have h2 : (∑ j ∈ Finset.range 20, (((1520 : ℝ) + (j : ℝ)) / 1600) ^ 2 *
    hpThetaJensenCellsBatch076Lower j * ((((1520 : ℝ) + (j : ℝ) + 1) / 1600) - (((1520 : ℝ) + (j :
    ℝ)) / 1600))) ≤
      ∑ j ∈ Finset.range 20,
        ∫ u : ℝ in Set.Ioo (((1520 : ℝ) + (j : ℝ)) / 1600) (((1520 : ℝ) + (j : ℝ) + 1) / 1600), u
          ^ 2 * hpRiemannThetaDifferentialKernel u := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch076_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 2
      (Or.inr (Or.inl rfl))).1
  have h4 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((1520 : ℝ) + (j : ℝ)) / 1600) (((1520 : ℝ) + (j : ℝ) + 1) / 1600), u ^
        4 * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((1520 : ℝ) + (j : ℝ) + 1) / 1600) ^ 4 *
        hpThetaJensenCellsBatch076Upper j * ((((1520 : ℝ) + (j : ℝ) + 1) / 1600) - (((1520 : ℝ) +
        (j : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch076_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 4
      (Or.inr (Or.inr rfl))).2
  rw [hs 0 (Or.inl rfl)] at h0
  rw [hs 2 (Or.inr (Or.inl rfl))] at h2
  rw [hs 4 (Or.inr (Or.inr rfl))] at h4
  norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch076Lower,
    hpThetaJensenCellsBatch076Upper] at h0 h2 h4
  norm_num [hpThetaJensenBatchZeroUpper, hpThetaJensenBatchSecondLower,
    hpThetaJensenBatchFourthUpper]
  exact ⟨le_trans h0 (by norm_num), le_trans (by norm_num) h2,
    le_trans h4 (by norm_num)⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Twenty rational terms are verified for each of the three moment orders.
theorem hpThetaJensenCellsBatch077_finiteIntegral_bounds :
    (∫ u : ℝ in Set.Ioo (77 / 80 : ℝ) ((77 + 1) / 80 : ℝ), u ^ 0 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchZeroUpper 77 ∧
    hpThetaJensenBatchSecondLower 77 ≤
        (∫ u : ℝ in Set.Ioo (77 / 80 : ℝ) ((77 + 1) / 80 : ℝ), u ^ 2 *
          hpRiemannThetaDifferentialKernel u) ∧
    (∫ u : ℝ in Set.Ioo (77 / 80 : ℝ) ((77 + 1) / 80 : ℝ), u ^ 4 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchFourthUpper 77 := by
  have hs (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
      (∑ j ∈ Finset.range 20, ∫ u : ℝ in Set.Ioo (((1540 : ℝ) + (j : ℝ)) / 1600) (((1540 : ℝ) + (j
        : ℝ) + 1) / 1600),
        u ^ m * hpRiemannThetaDifferentialKernel u) =
      ∫ u : ℝ in Set.Ioo (77 / 80 : ℝ) ((77 + 1) / 80 : ℝ), u ^ m *
        hpRiemannThetaDifferentialKernel u := by
    have h := hpThetaJensen_batchCellIntegral_sum m hm 77
    have hc : ∀ j : ℕ,
        Set.Ioo (((1540 : ℝ) + (j : ℝ)) / 1600) (((1540 : ℝ) + (j : ℝ) + 1) / 1600) =
          Set.Ioo ((77 : ℝ) / 80 + (j : ℝ) / 1600)
            ((77 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600) := by
      intro j
      have hl : (((1540 : ℝ) + (j : ℝ)) / 1600) = (77 : ℝ) / 80 + (j : ℝ) / 1600 := by ring
      have hr : (((1540 : ℝ) + (j : ℝ) + 1) / 1600) = (77 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600 :=
        by
        push_cast
        ring
      rw [hl, hr]
    simp_rw [hc]
    exact h
  have h0 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((1540 : ℝ) + (j : ℝ)) / 1600) (((1540 : ℝ) + (j : ℝ) + 1) / 1600), u ^
        0 * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((1540 : ℝ) + (j : ℝ) + 1) / 1600) ^ 0 *
        hpThetaJensenCellsBatch077Upper j * ((((1540 : ℝ) + (j : ℝ) + 1) / 1600) - (((1540 : ℝ) +
        (j : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch077_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 0
      (Or.inl rfl)).2
  have h2 : (∑ j ∈ Finset.range 20, (((1540 : ℝ) + (j : ℝ)) / 1600) ^ 2 *
    hpThetaJensenCellsBatch077Lower j * ((((1540 : ℝ) + (j : ℝ) + 1) / 1600) - (((1540 : ℝ) + (j :
    ℝ)) / 1600))) ≤
      ∑ j ∈ Finset.range 20,
        ∫ u : ℝ in Set.Ioo (((1540 : ℝ) + (j : ℝ)) / 1600) (((1540 : ℝ) + (j : ℝ) + 1) / 1600), u
          ^ 2 * hpRiemannThetaDifferentialKernel u := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch077_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 2
      (Or.inr (Or.inl rfl))).1
  have h4 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((1540 : ℝ) + (j : ℝ)) / 1600) (((1540 : ℝ) + (j : ℝ) + 1) / 1600), u ^
        4 * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((1540 : ℝ) + (j : ℝ) + 1) / 1600) ^ 4 *
        hpThetaJensenCellsBatch077Upper j * ((((1540 : ℝ) + (j : ℝ) + 1) / 1600) - (((1540 : ℝ) +
        (j : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch077_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 4
      (Or.inr (Or.inr rfl))).2
  rw [hs 0 (Or.inl rfl)] at h0
  rw [hs 2 (Or.inr (Or.inl rfl))] at h2
  rw [hs 4 (Or.inr (Or.inr rfl))] at h4
  norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch077Lower,
    hpThetaJensenCellsBatch077Upper] at h0 h2 h4
  norm_num [hpThetaJensenBatchZeroUpper, hpThetaJensenBatchSecondLower,
    hpThetaJensenBatchFourthUpper]
  exact ⟨le_trans h0 (by norm_num), le_trans (by norm_num) h2,
    le_trans h4 (by norm_num)⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Twenty rational terms are verified for each of the three moment orders.
theorem hpThetaJensenCellsBatch078_finiteIntegral_bounds :
    (∫ u : ℝ in Set.Ioo (78 / 80 : ℝ) ((78 + 1) / 80 : ℝ), u ^ 0 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchZeroUpper 78 ∧
    hpThetaJensenBatchSecondLower 78 ≤
        (∫ u : ℝ in Set.Ioo (78 / 80 : ℝ) ((78 + 1) / 80 : ℝ), u ^ 2 *
          hpRiemannThetaDifferentialKernel u) ∧
    (∫ u : ℝ in Set.Ioo (78 / 80 : ℝ) ((78 + 1) / 80 : ℝ), u ^ 4 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchFourthUpper 78 := by
  have hs (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
      (∑ j ∈ Finset.range 20, ∫ u : ℝ in Set.Ioo (((1560 : ℝ) + (j : ℝ)) / 1600) (((1560 : ℝ) + (j
        : ℝ) + 1) / 1600),
        u ^ m * hpRiemannThetaDifferentialKernel u) =
      ∫ u : ℝ in Set.Ioo (78 / 80 : ℝ) ((78 + 1) / 80 : ℝ), u ^ m *
        hpRiemannThetaDifferentialKernel u := by
    have h := hpThetaJensen_batchCellIntegral_sum m hm 78
    have hc : ∀ j : ℕ,
        Set.Ioo (((1560 : ℝ) + (j : ℝ)) / 1600) (((1560 : ℝ) + (j : ℝ) + 1) / 1600) =
          Set.Ioo ((78 : ℝ) / 80 + (j : ℝ) / 1600)
            ((78 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600) := by
      intro j
      have hl : (((1560 : ℝ) + (j : ℝ)) / 1600) = (78 : ℝ) / 80 + (j : ℝ) / 1600 := by ring
      have hr : (((1560 : ℝ) + (j : ℝ) + 1) / 1600) = (78 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600 :=
        by
        push_cast
        ring
      rw [hl, hr]
    simp_rw [hc]
    exact h
  have h0 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((1560 : ℝ) + (j : ℝ)) / 1600) (((1560 : ℝ) + (j : ℝ) + 1) / 1600), u ^
        0 * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((1560 : ℝ) + (j : ℝ) + 1) / 1600) ^ 0 *
        hpThetaJensenCellsBatch078Upper j * ((((1560 : ℝ) + (j : ℝ) + 1) / 1600) - (((1560 : ℝ) +
        (j : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch078_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 0
      (Or.inl rfl)).2
  have h2 : (∑ j ∈ Finset.range 20, (((1560 : ℝ) + (j : ℝ)) / 1600) ^ 2 *
    hpThetaJensenCellsBatch078Lower j * ((((1560 : ℝ) + (j : ℝ) + 1) / 1600) - (((1560 : ℝ) + (j :
    ℝ)) / 1600))) ≤
      ∑ j ∈ Finset.range 20,
        ∫ u : ℝ in Set.Ioo (((1560 : ℝ) + (j : ℝ)) / 1600) (((1560 : ℝ) + (j : ℝ) + 1) / 1600), u
          ^ 2 * hpRiemannThetaDifferentialKernel u := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch078_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 2
      (Or.inr (Or.inl rfl))).1
  have h4 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((1560 : ℝ) + (j : ℝ)) / 1600) (((1560 : ℝ) + (j : ℝ) + 1) / 1600), u ^
        4 * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((1560 : ℝ) + (j : ℝ) + 1) / 1600) ^ 4 *
        hpThetaJensenCellsBatch078Upper j * ((((1560 : ℝ) + (j : ℝ) + 1) / 1600) - (((1560 : ℝ) +
        (j : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch078_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 4
      (Or.inr (Or.inr rfl))).2
  rw [hs 0 (Or.inl rfl)] at h0
  rw [hs 2 (Or.inr (Or.inl rfl))] at h2
  rw [hs 4 (Or.inr (Or.inr rfl))] at h4
  norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch078Lower,
    hpThetaJensenCellsBatch078Upper] at h0 h2 h4
  norm_num [hpThetaJensenBatchZeroUpper, hpThetaJensenBatchSecondLower,
    hpThetaJensenBatchFourthUpper]
  exact ⟨le_trans h0 (by norm_num), le_trans (by norm_num) h2,
    le_trans h4 (by norm_num)⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Twenty rational terms are verified for each of the three moment orders.
theorem hpThetaJensenCellsBatch079_finiteIntegral_bounds :
    (∫ u : ℝ in Set.Ioo (79 / 80 : ℝ) ((79 + 1) / 80 : ℝ), u ^ 0 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchZeroUpper 79 ∧
    hpThetaJensenBatchSecondLower 79 ≤
        (∫ u : ℝ in Set.Ioo (79 / 80 : ℝ) ((79 + 1) / 80 : ℝ), u ^ 2 *
          hpRiemannThetaDifferentialKernel u) ∧
    (∫ u : ℝ in Set.Ioo (79 / 80 : ℝ) ((79 + 1) / 80 : ℝ), u ^ 4 *
      hpRiemannThetaDifferentialKernel u) ≤
        hpThetaJensenBatchFourthUpper 79 := by
  have hs (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
      (∑ j ∈ Finset.range 20, ∫ u : ℝ in Set.Ioo (((1580 : ℝ) + (j : ℝ)) / 1600) (((1580 : ℝ) + (j
        : ℝ) + 1) / 1600),
        u ^ m * hpRiemannThetaDifferentialKernel u) =
      ∫ u : ℝ in Set.Ioo (79 / 80 : ℝ) ((79 + 1) / 80 : ℝ), u ^ m *
        hpRiemannThetaDifferentialKernel u := by
    have h := hpThetaJensen_batchCellIntegral_sum m hm 79
    have hc : ∀ j : ℕ,
        Set.Ioo (((1580 : ℝ) + (j : ℝ)) / 1600) (((1580 : ℝ) + (j : ℝ) + 1) / 1600) =
          Set.Ioo ((79 : ℝ) / 80 + (j : ℝ) / 1600)
            ((79 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600) := by
      intro j
      have hl : (((1580 : ℝ) + (j : ℝ)) / 1600) = (79 : ℝ) / 80 + (j : ℝ) / 1600 := by ring
      have hr : (((1580 : ℝ) + (j : ℝ) + 1) / 1600) = (79 : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600 :=
        by
        push_cast
        ring
      rw [hl, hr]
    simp_rw [hc]
    exact h
  have h0 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((1580 : ℝ) + (j : ℝ)) / 1600) (((1580 : ℝ) + (j : ℝ) + 1) / 1600), u ^
        0 * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((1580 : ℝ) + (j : ℝ) + 1) / 1600) ^ 0 *
        hpThetaJensenCellsBatch079Upper j * ((((1580 : ℝ) + (j : ℝ) + 1) / 1600) - (((1580 : ℝ) +
        (j : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch079_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 0
      (Or.inl rfl)).2
  have h2 : (∑ j ∈ Finset.range 20, (((1580 : ℝ) + (j : ℝ)) / 1600) ^ 2 *
    hpThetaJensenCellsBatch079Lower j * ((((1580 : ℝ) + (j : ℝ) + 1) / 1600) - (((1580 : ℝ) + (j :
    ℝ)) / 1600))) ≤
      ∑ j ∈ Finset.range 20,
        ∫ u : ℝ in Set.Ioo (((1580 : ℝ) + (j : ℝ)) / 1600) (((1580 : ℝ) + (j : ℝ) + 1) / 1600), u
          ^ 2 * hpRiemannThetaDifferentialKernel u := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch079_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 2
      (Or.inr (Or.inl rfl))).1
  have h4 : (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo (((1580 : ℝ) + (j : ℝ)) / 1600) (((1580 : ℝ) + (j : ℝ) + 1) / 1600), u ^
        4 * hpRiemannThetaDifferentialKernel u) ≤
      ∑ j ∈ Finset.range 20, (((1580 : ℝ) + (j : ℝ) + 1) / 1600) ^ 4 *
        hpThetaJensenCellsBatch079Upper j * ((((1580 : ℝ) + (j : ℝ) + 1) / 1600) - (((1580 : ℝ) +
        (j : ℝ)) / 1600)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hpThetaJensenCellsBatch079_cellIntegral_bounds ⟨j, Finset.mem_range.mp hj⟩ 4
      (Or.inr (Or.inr rfl))).2
  rw [hs 0 (Or.inl rfl)] at h0
  rw [hs 2 (Or.inr (Or.inl rfl))] at h2
  rw [hs 4 (Or.inr (Or.inr rfl))] at h4
  norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch079Lower,
    hpThetaJensenCellsBatch079Upper] at h0 h2 h4
  norm_num [hpThetaJensenBatchZeroUpper, hpThetaJensenBatchSecondLower,
    hpThetaJensenBatchFourthUpper]
  exact ⟨le_trans h0 (by norm_num), le_trans (by norm_num) h2,
    le_trans h4 (by norm_num)⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- This finite split selects the already proved batch theorem.
theorem hpThetaJensen_batchFiniteIntegral_bounds (b : Fin 80) :
    (∫ u : ℝ in Set.Ioo ((b.val : ℝ) / 80) (((b.val : ℝ) + 1) / 80),
      u ^ 0 * hpRiemannThetaDifferentialKernel u) ≤ hpThetaJensenBatchZeroUpper b.val ∧
    hpThetaJensenBatchSecondLower b.val ≤
      (∫ u : ℝ in Set.Ioo ((b.val : ℝ) / 80) (((b.val : ℝ) + 1) / 80),
        u ^ 2 * hpRiemannThetaDifferentialKernel u) ∧
    (∫ u : ℝ in Set.Ioo ((b.val : ℝ) / 80) (((b.val : ℝ) + 1) / 80),
      u ^ 4 * hpRiemannThetaDifferentialKernel u) ≤ hpThetaJensenBatchFourthUpper b.val := by
  fin_cases b
  · have h := hpThetaJensenCellsBatch000_finiteIntegral_bounds
    norm_num at h ⊢
    exact h
  · have h := hpThetaJensenCellsBatch001_finiteIntegral_bounds
    norm_num at h ⊢
    exact h
  · have h := hpThetaJensenCellsBatch002_finiteIntegral_bounds
    norm_num at h ⊢
    exact h
  · have h := hpThetaJensenCellsBatch003_finiteIntegral_bounds
    norm_num at h ⊢
    exact h
  · have h := hpThetaJensenCellsBatch004_finiteIntegral_bounds
    norm_num at h ⊢
    exact h
  · have h := hpThetaJensenCellsBatch005_finiteIntegral_bounds
    norm_num at h ⊢
    exact h
  · have h := hpThetaJensenCellsBatch006_finiteIntegral_bounds
    norm_num at h ⊢
    exact h
  · have h := hpThetaJensenCellsBatch007_finiteIntegral_bounds
    norm_num at h ⊢
    exact h
  · have h := hpThetaJensenCellsBatch008_finiteIntegral_bounds
    norm_num at h ⊢
    exact h
  · have h := hpThetaJensenCellsBatch009_finiteIntegral_bounds
    norm_num at h ⊢
    exact h
  · have h := hpThetaJensenCellsBatch010_finiteIntegral_bounds
    norm_num at h ⊢
    exact h
  · have h := hpThetaJensenCellsBatch011_finiteIntegral_bounds
    norm_num at h ⊢
    exact h
  · have h := hpThetaJensenCellsBatch012_finiteIntegral_bounds
    norm_num at h ⊢
    exact h
  · have h := hpThetaJensenCellsBatch013_finiteIntegral_bounds
    norm_num at h ⊢
    exact h
  · have h := hpThetaJensenCellsBatch014_finiteIntegral_bounds
    norm_num at h ⊢
    exact h
  · have h := hpThetaJensenCellsBatch015_finiteIntegral_bounds
    norm_num at h ⊢
    exact h
  · have h := hpThetaJensenCellsBatch016_finiteIntegral_bounds
    norm_num at h ⊢
    exact h
  · have h := hpThetaJensenCellsBatch017_finiteIntegral_bounds
    norm_num at h ⊢
    exact h
  · have h := hpThetaJensenCellsBatch018_finiteIntegral_bounds
    norm_num at h ⊢
    exact h
  · have h := hpThetaJensenCellsBatch019_finiteIntegral_bounds
    norm_num at h ⊢
    exact h
  · have h := hpThetaJensenCellsBatch020_finiteIntegral_bounds
    norm_num at h ⊢
    exact h
  · have h := hpThetaJensenCellsBatch021_finiteIntegral_bounds
    norm_num at h ⊢
    exact h
  · have h := hpThetaJensenCellsBatch022_finiteIntegral_bounds
    norm_num at h ⊢
    exact h
  · have h := hpThetaJensenCellsBatch023_finiteIntegral_bounds
    norm_num at h ⊢
    exact h
  · have h := hpThetaJensenCellsBatch024_finiteIntegral_bounds
    norm_num at h ⊢
    exact h
  · have h := hpThetaJensenCellsBatch025_finiteIntegral_bounds
    norm_num at h ⊢
    exact h
  · have h := hpThetaJensenCellsBatch026_finiteIntegral_bounds
    norm_num at h ⊢
    exact h
  · have h := hpThetaJensenCellsBatch027_finiteIntegral_bounds
    norm_num at h ⊢
    exact h
  · have h := hpThetaJensenCellsBatch028_finiteIntegral_bounds
    norm_num at h ⊢
    exact h
  · have h := hpThetaJensenCellsBatch029_finiteIntegral_bounds
    norm_num at h ⊢
    exact h
  · have h := hpThetaJensenCellsBatch030_finiteIntegral_bounds
    norm_num at h ⊢
    exact h
  · have h := hpThetaJensenCellsBatch031_finiteIntegral_bounds
    norm_num at h ⊢
    exact h
  · have h := hpThetaJensenCellsBatch032_finiteIntegral_bounds
    norm_num at h ⊢
    exact h
  · have h := hpThetaJensenCellsBatch033_finiteIntegral_bounds
    norm_num at h ⊢
    exact h
  · have h := hpThetaJensenCellsBatch034_finiteIntegral_bounds
    norm_num at h ⊢
    exact h
  · have h := hpThetaJensenCellsBatch035_finiteIntegral_bounds
    norm_num at h ⊢
    exact h
  · have h := hpThetaJensenCellsBatch036_finiteIntegral_bounds
    norm_num at h ⊢
    exact h
  · have h := hpThetaJensenCellsBatch037_finiteIntegral_bounds
    norm_num at h ⊢
    exact h
  · have h := hpThetaJensenCellsBatch038_finiteIntegral_bounds
    norm_num at h ⊢
    exact h
  · have h := hpThetaJensenCellsBatch039_finiteIntegral_bounds
    norm_num at h ⊢
    exact h
  · have h := hpThetaJensenCellsBatch040_finiteIntegral_bounds
    norm_num at h ⊢
    exact h
  · have h := hpThetaJensenCellsBatch041_finiteIntegral_bounds
    norm_num at h ⊢
    exact h
  · have h := hpThetaJensenCellsBatch042_finiteIntegral_bounds
    norm_num at h ⊢
    exact h
  · have h := hpThetaJensenCellsBatch043_finiteIntegral_bounds
    norm_num at h ⊢
    exact h
  · have h := hpThetaJensenCellsBatch044_finiteIntegral_bounds
    norm_num at h ⊢
    exact h
  · have h := hpThetaJensenCellsBatch045_finiteIntegral_bounds
    norm_num at h ⊢
    exact h
  · have h := hpThetaJensenCellsBatch046_finiteIntegral_bounds
    norm_num at h ⊢
    exact h
  · have h := hpThetaJensenCellsBatch047_finiteIntegral_bounds
    norm_num at h ⊢
    exact h
  · have h := hpThetaJensenCellsBatch048_finiteIntegral_bounds
    norm_num at h ⊢
    exact h
  · have h := hpThetaJensenCellsBatch049_finiteIntegral_bounds
    norm_num at h ⊢
    exact h
  · have h := hpThetaJensenCellsBatch050_finiteIntegral_bounds
    norm_num at h ⊢
    exact h
  · have h := hpThetaJensenCellsBatch051_finiteIntegral_bounds
    norm_num at h ⊢
    exact h
  · have h := hpThetaJensenCellsBatch052_finiteIntegral_bounds
    norm_num at h ⊢
    exact h
  · have h := hpThetaJensenCellsBatch053_finiteIntegral_bounds
    norm_num at h ⊢
    exact h
  · have h := hpThetaJensenCellsBatch054_finiteIntegral_bounds
    norm_num at h ⊢
    exact h
  · have h := hpThetaJensenCellsBatch055_finiteIntegral_bounds
    norm_num at h ⊢
    exact h
  · have h := hpThetaJensenCellsBatch056_finiteIntegral_bounds
    norm_num at h ⊢
    exact h
  · have h := hpThetaJensenCellsBatch057_finiteIntegral_bounds
    norm_num at h ⊢
    exact h
  · have h := hpThetaJensenCellsBatch058_finiteIntegral_bounds
    norm_num at h ⊢
    exact h
  · have h := hpThetaJensenCellsBatch059_finiteIntegral_bounds
    norm_num at h ⊢
    exact h
  · have h := hpThetaJensenCellsBatch060_finiteIntegral_bounds
    norm_num at h ⊢
    exact h
  · have h := hpThetaJensenCellsBatch061_finiteIntegral_bounds
    norm_num at h ⊢
    exact h
  · have h := hpThetaJensenCellsBatch062_finiteIntegral_bounds
    norm_num at h ⊢
    exact h
  · have h := hpThetaJensenCellsBatch063_finiteIntegral_bounds
    norm_num at h ⊢
    exact h
  · have h := hpThetaJensenCellsBatch064_finiteIntegral_bounds
    norm_num at h ⊢
    exact h
  · have h := hpThetaJensenCellsBatch065_finiteIntegral_bounds
    norm_num at h ⊢
    exact h
  · have h := hpThetaJensenCellsBatch066_finiteIntegral_bounds
    norm_num at h ⊢
    exact h
  · have h := hpThetaJensenCellsBatch067_finiteIntegral_bounds
    norm_num at h ⊢
    exact h
  · have h := hpThetaJensenCellsBatch068_finiteIntegral_bounds
    norm_num at h ⊢
    exact h
  · have h := hpThetaJensenCellsBatch069_finiteIntegral_bounds
    norm_num at h ⊢
    exact h
  · have h := hpThetaJensenCellsBatch070_finiteIntegral_bounds
    norm_num at h ⊢
    exact h
  · have h := hpThetaJensenCellsBatch071_finiteIntegral_bounds
    norm_num at h ⊢
    exact h
  · have h := hpThetaJensenCellsBatch072_finiteIntegral_bounds
    norm_num at h ⊢
    exact h
  · have h := hpThetaJensenCellsBatch073_finiteIntegral_bounds
    norm_num at h ⊢
    exact h
  · have h := hpThetaJensenCellsBatch074_finiteIntegral_bounds
    norm_num at h ⊢
    exact h
  · have h := hpThetaJensenCellsBatch075_finiteIntegral_bounds
    norm_num at h ⊢
    exact h
  · have h := hpThetaJensenCellsBatch076_finiteIntegral_bounds
    norm_num at h ⊢
    exact h
  · have h := hpThetaJensenCellsBatch077_finiteIntegral_bounds
    norm_num at h ⊢
    exact h
  · have h := hpThetaJensenCellsBatch078_finiteIntegral_bounds
    norm_num at h ⊢
    exact h
  · have h := hpThetaJensenCellsBatch079_finiteIntegral_bounds
    norm_num at h ⊢
    exact h

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Eighty rounded rational batch bounds leave room for both proved tails.
theorem hpThetaJensen_finiteIntegral_numeric_bounds :
    (∫ u : ℝ in Set.Ioo 0 1, u ^ 0 * hpRiemannThetaDifferentialKernel u) ≤
      501 / 1000 - 1 / 50000000 ∧
    (227 / 10000 : ℝ) ≤
      (∫ u : ℝ in Set.Ioo 0 1, u ^ 2 * hpRiemannThetaDifferentialKernel u) ∧
    (∫ u : ℝ in Set.Ioo 0 1, u ^ 4 * hpRiemannThetaDifferentialKernel u) ≤
      3 / 1000 - 1 / 50000000 := by
  have h0 :
      (∑ b ∈ Finset.range 80,
        ∫ u : ℝ in Set.Ioo ((b : ℝ) / 80) (((b : ℝ) + 1) / 80),
          u ^ 0 * hpRiemannThetaDifferentialKernel u) ≤
      ∑ b ∈ Finset.range 80, hpThetaJensenBatchZeroUpper b := by
    apply Finset.sum_le_sum
    intro b hb
    exact (hpThetaJensen_batchFiniteIntegral_bounds
      ⟨b, Finset.mem_range.mp hb⟩).1
  have h2 :
      (∑ b ∈ Finset.range 80, hpThetaJensenBatchSecondLower b) ≤
      ∑ b ∈ Finset.range 80,
        ∫ u : ℝ in Set.Ioo ((b : ℝ) / 80) (((b : ℝ) + 1) / 80),
          u ^ 2 * hpRiemannThetaDifferentialKernel u := by
    apply Finset.sum_le_sum
    intro b hb
    exact (hpThetaJensen_batchFiniteIntegral_bounds
      ⟨b, Finset.mem_range.mp hb⟩).2.1
  have h4 :
      (∑ b ∈ Finset.range 80,
        ∫ u : ℝ in Set.Ioo ((b : ℝ) / 80) (((b : ℝ) + 1) / 80),
          u ^ 4 * hpRiemannThetaDifferentialKernel u) ≤
      ∑ b ∈ Finset.range 80, hpThetaJensenBatchFourthUpper b := by
    apply Finset.sum_le_sum
    intro b hb
    exact (hpThetaJensen_batchFiniteIntegral_bounds
      ⟨b, Finset.mem_range.mp hb⟩).2.2
  have hs (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
      (∑ b ∈ Finset.range 80,
        ∫ u : ℝ in Set.Ioo ((b : ℝ) / 80) (((b : ℝ) + 1) / 80),
          u ^ m * hpRiemannThetaDifferentialKernel u) =
      ∫ u : ℝ in Set.Ioo 0 1, u ^ m * hpRiemannThetaDifferentialKernel u := by
    simpa only [Nat.cast_add, Nat.cast_one] using hpThetaJensen_80BatchIntegral_sum m hm
  rw [hs 0 (Or.inl rfl)] at h0
  rw [hs 2 (Or.inr (Or.inl rfl))] at h2
  rw [hs 4 (Or.inr (Or.inr rfl))] at h4
  norm_num [Finset.sum_range_succ, hpThetaJensenBatchZeroUpper,
    hpThetaJensenBatchSecondLower, hpThetaJensenBatchFourthUpper] at h0 h2 h4
  simp only [pow_zero, one_mul]
  exact ⟨le_trans h0 (by norm_num), le_trans (by norm_num) h2,
    le_trans h4 (by norm_num)⟩

#print axioms hpThetaJensen_batchFiniteIntegral_bounds
#print axioms hpThetaJensen_finiteIntegral_numeric_bounds
end HodgeProofHP
