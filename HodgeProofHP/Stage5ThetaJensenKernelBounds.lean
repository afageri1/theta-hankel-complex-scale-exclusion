import HodgeProofHP.Stage4ThetaKernelFirstTermUpper
import HodgeProofHP.Stage4ThetaTraceEndpointLowerBound
import Mathlib.Tactic

/-!
# Analytic kernel bounds for the Jensen interval certificates

The endpoint bounds enclose the actual differential theta kernel on each
nonnegative interval. They also bound its nonnegative power weights.
The tail envelope uses exp(2u) >= exp(2p) * (1 + 2(u-p)).

No JSON data, external numerical result, or moment inequality is assumed.
The numerical endpoint certificates and integral assembly are later steps.
-/

noncomputable section

namespace HodgeProofHP

def hpThetaJensenKernelEndpointUpper (l r : ℝ) : ℝ :=
  (12183 / 12151 : ℝ) *
    ((4 * (Real.pi * Real.exp (2 * r)) ^ 2 -
      6 * (Real.pi * Real.exp (2 * r))) *
      (2 * Real.exp (r / 2 - Real.pi * Real.exp (2 * l))))

theorem hpThetaJensenKernelEndpointUpper_nonneg
    (l r : ℝ) (hr : 0 ≤ r) :
    0 ≤ hpThetaJensenKernelEndpointUpper l r := by
  have hb := hpThetaTrace_pi_exp_ge_three r hr
  have hpoly : 0 ≤ 4 * (Real.pi * Real.exp (2 * r)) ^ 2 -
      6 * (Real.pi * Real.exp (2 * r)) := by
    nlinarith
  unfold hpThetaJensenKernelEndpointUpper
  exact mul_nonneg (by norm_num) (mul_nonneg hpoly (by positivity))

theorem hpThetaJensenKernel_le_endpointUpper
    (l r u : ℝ) (hl : 0 ≤ l) (hlu : l ≤ u) (hur : u ≤ r) :
    hpRiemannThetaDifferentialKernel u ≤
      hpThetaJensenKernelEndpointUpper l r := by
  have hu : 0 ≤ u := le_trans hl hlu
  have hr : 0 ≤ r := le_trans hu hur
  have hel : Real.exp (2 * l) ≤ Real.exp (2 * u) :=
    Real.exp_le_exp.mpr (by linarith)
  have her : Real.exp (2 * u) ≤ Real.exp (2 * r) :=
    Real.exp_le_exp.mpr (by linarith)
  have hbl := mul_le_mul_of_nonneg_left hel (le_of_lt Real.pi_pos)
  have hbr := mul_le_mul_of_nonneg_left her (le_of_lt Real.pi_pos)
  have hpoly := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (2 * u)) (Real.pi * Real.exp (2 * r))
    (hpThetaTrace_pi_exp_ge_three u hu) hbr
  have hpr := hpThetaTrace_pi_exp_ge_three r hr
  have hpoly0 : 0 ≤ 4 * (Real.pi * Real.exp (2 * r)) ^ 2 -
      6 * (Real.pi * Real.exp (2 * r)) := by
    nlinarith
  have hexp :
      2 * Real.exp (u / 2 - Real.pi * Real.exp (2 * u)) ≤
        2 * Real.exp (r / 2 - Real.pi * Real.exp (2 * l)) := by
    apply mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by linarith)) (by norm_num)
  have hfirst : hpThetaGaussianKernelTerm Real.pi u ≤
      (4 * (Real.pi * Real.exp (2 * r)) ^ 2 -
        6 * (Real.pi * Real.exp (2 * r))) *
        (2 * Real.exp (r / 2 - Real.pi * Real.exp (2 * l))) := by
    have h := mul_le_mul hpoly hexp
      (by positivity :
        0 ≤ 2 * Real.exp (u / 2 - Real.pi * Real.exp (2 * u))) hpoly0
    calc
      hpThetaGaussianKernelTerm Real.pi u =
          (4 * (Real.pi * Real.exp (2 * u)) ^ 2 -
            6 * (Real.pi * Real.exp (2 * u))) *
            (2 * Real.exp (u / 2 - Real.pi * Real.exp (2 * u))) := by
        unfold hpThetaGaussianKernelTerm hpThetaGaussianProfile
        ring
      _ ≤ _ := h
  exact le_trans (hpThetaPhi_le_firstTerm_upper u hu)
    (mul_le_mul_of_nonneg_left hfirst (by norm_num))

theorem hpThetaJensenKernel_endpointLower_le
    (l r u : ℝ) (hl : 0 ≤ l) (hlu : l ≤ u) (hur : u ≤ r) :
    hpThetaTraceEndpointLower l r ≤ hpRiemannThetaDifferentialKernel u := by
  exact le_trans (hpThetaTraceEndpointLower_le_firstTerm l r u hl hlu hur)
    (hpThetaTraceFirstTerm_le_phi u (le_trans hl hlu))

theorem hpThetaJensenKernel_weighted_endpointLower_le
    (m : ℕ) (l r u : ℝ) (hl : 0 ≤ l) (hlu : l ≤ u) (hur : u ≤ r) :
    l ^ m * hpThetaTraceEndpointLower l r ≤
      u ^ m * hpRiemannThetaDifferentialKernel u := by
  exact mul_le_mul (pow_le_pow_left₀ hl hlu m)
    (hpThetaJensenKernel_endpointLower_le l r u hl hlu hur)
    (hpThetaTraceEndpointLower_nonneg l r hl)
    (pow_nonneg (le_trans hl hlu) m)

theorem hpThetaJensenKernel_weighted_le_endpointUpper
    (m : ℕ) (l r u : ℝ) (hl : 0 ≤ l) (hlu : l ≤ u) (hur : u ≤ r) :
    u ^ m * hpRiemannThetaDifferentialKernel u ≤
      r ^ m * hpThetaJensenKernelEndpointUpper l r := by
  have hu : 0 ≤ u := le_trans hl hlu
  exact mul_le_mul (pow_le_pow_left₀ hu hur m)
    (hpThetaJensenKernel_le_endpointUpper l r u hl hlu hur)
    (le_of_lt (hpThetaPhi_pos_on_nonnegative u hu))
    (pow_nonneg (le_trans hu hur) m)

def hpThetaJensenKernelTailRate (p : ℝ) : ℝ :=
  2 * Real.pi * Real.exp (2 * p) - 9 / 2

def hpThetaJensenKernelTailAmplitude (p : ℝ) : ℝ :=
  (12183 / 12151 : ℝ) * (8 * Real.pi ^ 2) *
    Real.exp ((9 / 2 : ℝ) * p - Real.pi * Real.exp (2 * p))

theorem hpThetaJensenKernelTailRate_pos (p : ℝ) (hp : 0 ≤ p) :
    0 < hpThetaJensenKernelTailRate p := by
  have h := hpThetaTrace_pi_exp_ge_three p hp
  unfold hpThetaJensenKernelTailRate
  linarith

theorem hpThetaJensenKernelTailAmplitude_pos (p : ℝ) :
    0 < hpThetaJensenKernelTailAmplitude p := by
  unfold hpThetaJensenKernelTailAmplitude
  positivity

theorem hpThetaJensenKernel_firstTerm_le_simple (u : ℝ) :
    hpThetaGaussianKernelTerm Real.pi u ≤
      8 * Real.pi ^ 2 *
        Real.exp ((9 / 2 : ℝ) * u - Real.pi * Real.exp (2 * u)) := by
  have hcoeff :
      4 * Real.pi ^ 2 * Real.exp (2 * u) ^ 2 -
        6 * Real.pi * Real.exp (2 * u) ≤
      4 * Real.pi ^ 2 * Real.exp (2 * u) ^ 2 := by
    have h : 0 ≤ 6 * Real.pi * Real.exp (2 * u) := by positivity
    linarith
  unfold hpThetaGaussianKernelTerm hpThetaGaussianProfile
  calc
    _ ≤ (4 * Real.pi ^ 2 * Real.exp (2 * u) ^ 2) *
        (2 * Real.exp (u / 2 - Real.pi * Real.exp (2 * u))) :=
      mul_le_mul_of_nonneg_right hcoeff (by positivity)
    _ = _ := by
      rw [show (9 / 2 : ℝ) * u - Real.pi * Real.exp (2 * u) =
        (2 * u + 2 * u) + (u / 2 - Real.pi * Real.exp (2 * u)) by ring,
        Real.exp_add, Real.exp_add]
      ring

theorem hpThetaJensenKernel_le_tailEnvelope
    (p u : ℝ) (hp : 0 ≤ p) (hpu : p ≤ u) :
    hpRiemannThetaDifferentialKernel u ≤
      hpThetaJensenKernelTailAmplitude p *
        Real.exp (-hpThetaJensenKernelTailRate p * (u - p)) := by
  have hu : 0 ≤ u := le_trans hp hpu
  have hexp :
      Real.exp (2 * p) * (1 + 2 * (u - p)) ≤ Real.exp (2 * u) := by
    have h := mul_le_mul_of_nonneg_left
      (Real.add_one_le_exp (2 * (u - p)))
      (le_of_lt (Real.exp_pos (2 * p)))
    calc
      _ ≤ Real.exp (2 * p) * Real.exp (2 * (u - p)) := by
        simpa only [add_comm] using h
      _ = _ := by
        rw [← Real.exp_add]
        congr 1
        ring
  have hscaled := mul_le_mul_of_nonneg_left hexp (le_of_lt Real.pi_pos)
  have harg :
      (9 / 2 : ℝ) * u - Real.pi * Real.exp (2 * u) ≤
        (9 / 2 : ℝ) * p - Real.pi * Real.exp (2 * p) -
          (2 * Real.pi * Real.exp (2 * p) - 9 / 2) * (u - p) := by
    calc
      _ ≤ (9 / 2 : ℝ) * u -
          Real.pi * (Real.exp (2 * p) * (1 + 2 * (u - p))) := by
        linarith
      _ = _ := by ring
  calc
    hpRiemannThetaDifferentialKernel u ≤
        (12183 / 12151 : ℝ) * (8 * Real.pi ^ 2 *
          Real.exp ((9 / 2 : ℝ) * u - Real.pi * Real.exp (2 * u))) :=
      le_trans (hpThetaPhi_le_firstTerm_upper u hu)
        (mul_le_mul_of_nonneg_left
          (hpThetaJensenKernel_firstTerm_le_simple u) (by norm_num))
    _ = ((12183 / 12151 : ℝ) * (8 * Real.pi ^ 2)) *
        Real.exp ((9 / 2 : ℝ) * u - Real.pi * Real.exp (2 * u)) := by ring
    _ ≤ ((12183 / 12151 : ℝ) * (8 * Real.pi ^ 2)) *
        Real.exp ((9 / 2 : ℝ) * p - Real.pi * Real.exp (2 * p) -
          (2 * Real.pi * Real.exp (2 * p) - 9 / 2) * (u - p)) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr harg) (by positivity)
    _ = _ := by
      unfold hpThetaJensenKernelTailAmplitude hpThetaJensenKernelTailRate
      rw [show (9 / 2 : ℝ) * p - Real.pi * Real.exp (2 * p) -
        (2 * Real.pi * Real.exp (2 * p) - 9 / 2) * (u - p) =
        ((9 / 2 : ℝ) * p - Real.pi * Real.exp (2 * p)) +
        (-(2 * Real.pi * Real.exp (2 * p) - 9 / 2) * (u - p)) by ring,
        Real.exp_add]
      ring

#print axioms hpThetaJensenKernelEndpointUpper_nonneg
#print axioms hpThetaJensenKernel_le_endpointUpper
#print axioms hpThetaJensenKernel_endpointLower_le
#print axioms hpThetaJensenKernel_weighted_endpointLower_le
#print axioms hpThetaJensenKernel_weighted_le_endpointUpper
#print axioms hpThetaJensenKernelTailRate_pos
#print axioms hpThetaJensenKernelTailAmplitude_pos
#print axioms hpThetaJensenKernel_firstTerm_le_simple
#print axioms hpThetaJensenKernel_le_tailEnvelope

end HodgeProofHP
