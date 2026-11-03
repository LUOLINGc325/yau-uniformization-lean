import Yau.Proofs.F04PositiveScalarPairing

open MeasureTheory Filter
open scoped Topology InnerProductSpace

noncomputable section

namespace Yau.F04Proof

/-- Ordered actual scalar L2 representatives have the expected signed
 pairing against every nonnegative actual L2 test. -/
theorem lp_inner_sub_nonpos_of_ae
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (f q w : Lp ℝ 2 μ)
    (hfq : ∀ᵐ x ∂μ, f x ≤ q x) (hw : ∀ᵐ x ∂μ, 0 ≤ w x) :
    inner ℝ (f - q) w ≤ 0 := by
  rw [L2.inner_def]
  apply integral_nonpos_of_ae
  filter_upwards [hfq, hw, Lp.coeFn_sub f q] with x hfx hwx hs
  rw [hs]
  simp only [Pi.sub_apply, RCLike.inner_apply, conj_trivial]
  exact mul_nonpos_of_nonneg_of_nonpos hwx (sub_nonpos.mpr hfx)

end Yau.F04Proof
