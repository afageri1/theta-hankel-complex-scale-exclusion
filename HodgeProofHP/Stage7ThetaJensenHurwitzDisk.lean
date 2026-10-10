import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# A disk step for Hurwitz zero exclusion

Apply the maximum modulus principle to the reciprocal of a nonvanishing
holomorphic function. A positive boundary lower bound is also a lower bound
at the center. Uniform limits inherit center nonvanishing when the limit is
nonzero on the boundary. The isolated-zero and Jensen-family applications
are subsequent obligations; no global zero exclusion is asserted here.
-/

noncomputable section
open Filter Set Metric
open scoped Topology

namespace HodgeProofHP

theorem hpComplexDisk_norm_lower_bound
    (f : ℂ → ℂ) (a : ℂ) (r m : ℝ) (hr : 0 < r) (hm : 0 < m)
    (hf : DiffContOnCl ℂ f (ball a r))
    (hnz : ∀ z ∈ closedBall a r, f z ≠ 0)
    (hboundary : ∀ z ∈ frontier (ball a r), m ≤ ‖f z‖) :
    m ≤ ‖f a‖ := by
  have ha : a ∈ ball a r := mem_ball_self hr
  have ha' : a ∈ closedBall a r := ball_subset_closedBall ha
  have hinv : DiffContOnCl ℂ (fun z => (f z)⁻¹) (ball a r) :=
    hf.inv (fun z hz => hnz z (closure_ball_subset_closedBall hz))
  have hbound : ∀ z ∈ frontier (ball a r), ‖(f z)⁻¹‖ ≤ m⁻¹ := by
    intro z hz
    rw [norm_inv]
    exact (inv_le_inv₀ (lt_of_lt_of_le hm (hboundary z hz)) hm).mpr
      (hboundary z hz)
  have hcenter := Complex.norm_le_of_forall_mem_frontier_norm_le
    (isBounded_ball : Bornology.IsBounded (ball a r)) hinv hbound
    (subset_closure ha)
  rw [norm_inv] at hcenter
  exact (inv_le_inv₀ (norm_pos_iff.mpr (hnz a ha')) hm).mp hcenter

theorem hpComplexDisk_uniformLimit_ne_zero
    (P : ℕ → ℂ → ℂ) (f : ℂ → ℂ) (a : ℂ) (r : ℝ) (hr : 0 < r)
    (hconv : TendstoUniformlyOn P f atTop (closedBall a r))
    (hf : ContinuousOn f (closedBall a r))
    (hboundary : ∀ z ∈ frontier (ball a r), f z ≠ 0)
    (hP : ∀ᶠ d : ℕ in atTop,
      DiffContOnCl ℂ (P d) (ball a r) ∧
        ∀ z ∈ closedBall a r, P d z ≠ 0) :
    f a ≠ 0 := by
  have hfront : frontier (ball a r) ⊆ closedBall a r :=
    frontier_subset_closure.trans closure_ball_subset_closedBall
  have hc : IsCompact (frontier (ball a r)) :=
    (isCompact_closedBall a r).of_isClosed_subset isClosed_frontier hfront
  obtain ⟨m, hm, hmin⟩ := hc.exists_forall_le'
    (hf.norm.mono hfront) (fun z hz => norm_pos_iff.mpr (hboundary z hz))
  have he : ∀ᶠ d : ℕ in atTop, ∀ z ∈ closedBall a r,
      dist (f z) (P d z) < m / 2 :=
    Metric.tendstoUniformlyOn_iff.mp hconv (m / 2) (by positivity)
  have hlower : ∀ᶠ d : ℕ in atTop, m / 2 ≤ ‖P d a‖ := by
    filter_upwards [hP, he] with d hd he
    apply hpComplexDisk_norm_lower_bound (P d) a r (m / 2) hr (by positivity)
      hd.1 hd.2
    intro z hz
    have h1 := hmin z hz
    have h2 := he z (hfront hz)
    have h3 := norm_sub_norm_le (f z) (P d z)
    rw [dist_eq_norm] at h2
    linarith
  have ha : a ∈ closedBall a r := ball_subset_closedBall (mem_ball_self hr)
  have hlim : Tendsto (fun d : ℕ => ‖P d a‖) atTop (𝓝 ‖f a‖) :=
    (hconv.tendsto_at ha).norm
  have hfa : m / 2 ≤ ‖f a‖ := ge_of_tendsto hlim hlower
  exact norm_pos_iff.mp (lt_of_lt_of_le (by positivity : 0 < m / 2) hfa)

#print axioms hpComplexDisk_norm_lower_bound
#print axioms hpComplexDisk_uniformLimit_ne_zero

end HodgeProofHP
