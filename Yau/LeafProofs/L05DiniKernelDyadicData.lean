import Yau.LeafProofs.L05DiniKernelSeries
import Mathlib.MeasureTheory.Constructions.Polish.Basic

noncomputable section

open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.LeafProofs.L05Aux

theorem diniDyadicAverage_measurable {psi : ℝ → ℝ} (hm : Measurable psi) :
    Measurable (diniDyadicAverage psi) := by
  apply Measurable.tsum
  intro k
  exact measurable_const.mul (hm.comp (measurable_const.mul measurable_id))

theorem diniDyadicAverage_data {psi : ℝ → ℝ} {eta B : ℝ}
    (he : 0 < eta) (he1 : eta < 1) (hB : 0 ≤ B) (hm : Measurable psi) (hzero : psi 0=0)
    (hmono : MonotoneOn psi (Set.Ioi (0:ℝ)))
    (hpsi : ∀ s : ℝ, 0 < s → 0 ≤ psi s ∧ psi s ≤ B*s^eta) :
    Measurable (diniDyadicAverage psi) ∧ diniDyadicAverage psi 0=0 ∧
      MonotoneOn (diniDyadicAverage psi) (Set.Ioi (0:ℝ)) ∧
      (∀ s : ℝ, 0 < s → 0 ≤ diniDyadicAverage psi s ∧ diniDyadicAverage psi s ≤ (2*B)*s^eta) := by
  refine ⟨diniDyadicAverage_measurable hm,by simp [diniDyadicAverage,hzero],?_,?_⟩
  · intro r hr s hs hrs
    have hSr := (diniDyadicAverage_summable he he1 hB hr hpsi).1
    have hSs := (diniDyadicAverage_summable he he1 hB hs hpsi).1
    apply hSr.tsum_le_tsum _ hSs
    intro k
    have hp : 0 < (2:ℝ)^k := pow_pos (by norm_num) _
    exact mul_le_mul_of_nonneg_left (hmono (mul_pos hp hr) (mul_pos hp hs)
      (mul_le_mul_of_nonneg_left hrs hp.le)) (pow_nonneg (by norm_num) _)
  · intro s hs
    refine ⟨tsum_nonneg (fun k => ?_),(diniDyadicAverage_summable he he1 hB hs hpsi).2⟩
    exact mul_nonneg (pow_nonneg (by norm_num) _)
      (hpsi ((2:ℝ)^k*s) (mul_pos (pow_pos (by norm_num) _) hs)).1

end Yau.LeafProofs.L05Aux
