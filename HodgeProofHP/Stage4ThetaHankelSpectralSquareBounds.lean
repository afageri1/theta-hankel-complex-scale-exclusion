import HodgeProofHP.Stage4ThetaHankelFourthMomentInvariant
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
Bounds for the sum of squared spectral values of the adjoint square.
The total spectral mass is the first trace energy.
-/

noncomputable section

namespace HodgeProofHP

theorem hpThetaHankelSpectralValue_re_nonneg
    (i : HPThetaHankelSpectralIndex) :
    0 ≤ i.1.re := by
  rw [hpThetaHankelSpectralValue_re_eq_energy]
  exact sq_nonneg _

theorem hpThetaHankelSpectralValue_re_le_total_energy
    (i : HPThetaHankelSpectralIndex) :
    i.1.re ≤ hpThetaFirstTraceEnergy := by
  have hs := hpThetaHankelSpectralValues_re_hasSum
  calc
    i.1.re ≤ ∑' j : HPThetaHankelSpectralIndex, j.1.re :=
      hs.summable.le_tsum i
        (fun j _ => hpThetaHankelSpectralValue_re_nonneg j)
    _ = hpThetaFirstTraceEnergy := hs.tsum_eq

theorem hpThetaHankelSpectralValue_re_sq_le_square_energy
    (i : HPThetaHankelSpectralIndex) :
    i.1.re ^ 2 ≤ hpThetaHankelSpectralSquareEnergy := by
  have hs := hpThetaHankelSpectralSquares_real_hasSum
  calc
    i.1.re ^ 2 ≤ ∑' j : HPThetaHankelSpectralIndex, j.1.re ^ 2 :=
      hs.summable.le_tsum i (fun j _ => sq_nonneg j.1.re)
    _ = hpThetaHankelSpectralSquareEnergy := hs.tsum_eq

theorem hpThetaHankelSpectralSquareEnergy_le_total_energy_sq :
    hpThetaHankelSpectralSquareEnergy ≤
      hpThetaFirstTraceEnergy ^ 2 := by
  have hs := hpThetaHankelSpectralValues_re_hasSum
  have hq := hpThetaHankelSpectralSquares_real_hasSum
  have hmajor :
      HasSum
        (fun i : HPThetaHankelSpectralIndex =>
          hpThetaFirstTraceEnergy * i.1.re)
        (hpThetaFirstTraceEnergy * hpThetaFirstTraceEnergy) :=
    hs.mul_left hpThetaFirstTraceEnergy
  have hpoint :
      ∀ i : HPThetaHankelSpectralIndex,
        i.1.re ^ 2 ≤ hpThetaFirstTraceEnergy * i.1.re := by
    intro i
    simpa only [pow_two] using
      mul_le_mul_of_nonneg_right
        (hpThetaHankelSpectralValue_re_le_total_energy i)
        (hpThetaHankelSpectralValue_re_nonneg i)
  calc
    hpThetaHankelSpectralSquareEnergy =
        ∑' i : HPThetaHankelSpectralIndex, i.1.re ^ 2 :=
      hq.tsum_eq.symm
    _ ≤ ∑' i : HPThetaHankelSpectralIndex,
        hpThetaFirstTraceEnergy * i.1.re :=
      Summable.tsum_le_tsum hpoint hq.summable hmajor.summable
    _ = hpThetaFirstTraceEnergy ^ 2 := by
      simpa only [pow_two] using hmajor.tsum_eq

theorem hpThetaHankelSpectralEnergyDifference_nonneg :
    0 ≤ hpThetaFirstTraceEnergy ^ 2 -
      hpThetaHankelSpectralSquareEnergy :=
  sub_nonneg.mpr
    hpThetaHankelSpectralSquareEnergy_le_total_energy_sq

#print axioms hpThetaHankelSpectralValue_re_nonneg
#print axioms hpThetaHankelSpectralValue_re_le_total_energy
#print axioms hpThetaHankelSpectralValue_re_sq_le_square_energy
#print axioms hpThetaHankelSpectralSquareEnergy_le_total_energy_sq
#print axioms hpThetaHankelSpectralEnergyDifference_nonneg

end HodgeProofHP
