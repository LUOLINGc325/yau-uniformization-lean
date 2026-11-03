import Yau.Proofs.F04PositiveEnergyHilbert

open MeasureTheory Filter Set
open scoped Topology InnerProductSpace

noncomputable section

namespace Yau.F04Proof

theorem l2_posPart_pairing {X : Type*} [MeasurableSpace X] (μ : Measure X) (f : Lp ℝ 2 μ) :
    inner ℝ f (Lp.posPart f) = ‖Lp.posPart f‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_posPart f] with x hx
  simp only [RCLike.inner_apply, conj_trivial, hx]
  rcases le_total 0 (f x) with h | h
  · rw [max_eq_left h]
  · rw [max_eq_right h, mul_zero, zero_mul]

end Yau.F04Proof
