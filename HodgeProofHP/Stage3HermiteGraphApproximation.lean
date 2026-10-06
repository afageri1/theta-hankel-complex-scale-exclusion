import HodgeProofHP.Stage3HermiteWeightedDomain
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Finite Hermite approximation of the operator graph
Finite Hermite sums converge both to a domain vector and,
after applying the closure, to its operator image.
-/

noncomputable section

open Filter
open scoped Topology

namespace HodgeProofHP

def hpHermiteTruncation (N : ℕ) (v : HPSpace) : HPSpace :=
  ∑ n ∈ Finset.range N,
    hpHermiteCoefficient v n • hpHermiteNormalizedL2 n

def hpHermiteTruncationVector (N : ℕ) (v : HPSpace) :
    HPHarmonicClosure.domain :=
  ∑ n ∈ Finset.range N,
    hpHermiteCoefficient v n • hpHermiteNormalizedClosureVector n

theorem hpHermiteTruncationVector_coe (N : ℕ) (v : HPSpace) :
    (hpHermiteTruncationVector N v : HPSpace) =
      hpHermiteTruncation N v := by
  change
    HPHarmonicClosure.domain.subtype
      (∑ n ∈ Finset.range N,
        hpHermiteCoefficient v n •
          hpHermiteNormalizedClosureVector n) =
    ∑ n ∈ Finset.range N,
      hpHermiteCoefficient v n • hpHermiteNormalizedL2 n
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [map_smul]
  rfl

theorem hpHermiteTruncation_mem_domain (N : ℕ) (v : HPSpace) :
    hpHermiteTruncation N v ∈ HPHarmonicClosure.domain := by
  rw [← hpHermiteTruncationVector_coe]
  exact (hpHermiteTruncationVector N v).property

theorem hpHermiteTruncationVector_action (N : ℕ) (v : HPSpace) :
    HPHarmonicClosure.toFun (hpHermiteTruncationVector N v) =
      ∑ n ∈ Finset.range N,
        ((2 * (n : ℂ) + 1) * hpHermiteCoefficient v n) •
          hpHermiteNormalizedL2 n := by
  unfold hpHermiteTruncationVector
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [map_smul, hpHermiteNormalized_closure_eigen]
  simp only [smul_smul]
  rw [mul_comm]

theorem hpHermiteTruncation_tendsto (v : HPSpace) :
    Tendsto (fun N : ℕ => hpHermiteTruncation N v)
      atTop (𝓝 v) := by
  exact (hpHermite_hasSum v).tendsto_sum_nat

theorem hpHermiteTruncationVector_coe_tendsto (v : HPSpace) :
    Tendsto
      (fun N : ℕ => (hpHermiteTruncationVector N v : HPSpace))
      atTop (𝓝 v) := by
  simpa only [hpHermiteTruncationVector_coe]
    using hpHermiteTruncation_tendsto v

theorem hpHermiteTruncationVector_action_tendsto
    (f : HPHarmonicClosure.domain) :
    Tendsto
      (fun N : ℕ =>
        HPHarmonicClosure.toFun
          (hpHermiteTruncationVector N (f : HPSpace)))
      atTop (𝓝 (HPHarmonicClosure.toFun f)) := by
  simpa only [hpHermiteTruncationVector_action]
    using (hpHermite_closure_action_hasSum f).tendsto_sum_nat

theorem hpHermite_graph_approximation
    (f : HPHarmonicClosure.domain) :
    Tendsto
      (fun N : ℕ =>
        (hpHermiteTruncationVector N (f : HPSpace) : HPSpace))
      atTop (𝓝 (f : HPSpace)) ∧
    Tendsto
      (fun N : ℕ =>
        HPHarmonicClosure.toFun
          (hpHermiteTruncationVector N (f : HPSpace)))
      atTop (𝓝 (HPHarmonicClosure.toFun f)) :=
  ⟨hpHermiteTruncationVector_coe_tendsto (f : HPSpace),
    hpHermiteTruncationVector_action_tendsto f⟩

end HodgeProofHP

#print axioms HodgeProofHP.hpHermiteTruncationVector_coe
#print axioms HodgeProofHP.hpHermiteTruncation_mem_domain
#print axioms HodgeProofHP.hpHermiteTruncationVector_action
#print axioms HodgeProofHP.hpHermiteTruncation_tendsto
#print axioms HodgeProofHP.hpHermiteTruncationVector_action_tendsto
#print axioms HodgeProofHP.hpHermite_graph_approximation
