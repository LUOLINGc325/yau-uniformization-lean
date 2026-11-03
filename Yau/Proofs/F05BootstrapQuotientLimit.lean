import Yau.Proofs.F05BootstrapGoodQuotient

/-! The actual good derivative is the uniform value limit of the forward
spatial or backward temporal quotients, with one common Holder bound. -/

open Set Filter
open scoped Topology
noncomputable section
set_option maxHeartbeats 1400000
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux
variable {n : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem F05_good_quotients_uniform_limit {ν d : Option (RIdx n)} {T α C : ℝ}
    (hα : 0 < α) {u : Point n → V} {Q K : Set (Point n)} {h : ℕ → ℝ}
    (hh : ∀ k, 0 < h k) (hZero : Tendsto h atTop (𝓝 0))
    (hGood : F05GoodDiffOn T d u (F05PosPatch ν T))
    (hSegment : ∀ k p, p ∈ Q → ∀ θ ∈ Icc (0 : ℝ) 1,
      F05GoodSegment d (h k) p θ ∈ F05PosPatch ν T)
    (hIn : ∀ k p, p ∈ Q → ∀ θ ∈ Icc (0 : ℝ) 1, F05GoodSegment d (h k) p θ ∈ K)
    (hHolder : HolderBound α K (F05GoodPartial T d u) C) :
    (∀ k, HolderBound α Q (F05GoodQuotient d (h k) u) C) ∧
      TendstoUniformlyOn (fun k => F05GoodQuotient d (h k) u) (F05GoodPartial T d u) atTop Q := by
  have hExponent : 0 < F05GoodExponent d α := by cases d <;> dsimp only [F05GoodExponent] <;> positivity
  have hError : ∀ k p, p ∈ Q →
      ‖F05GoodQuotient d (h k) u p-F05GoodPartial T d u p‖ ≤ C*(h k)^(F05GoodExponent d α) := by
    intro k
    exact F05_good_quotient_uniform_error (hh k) hα hGood (hSegment k) (hIn k) hHolder
  have hPower : Tendsto (fun k => C*(h k)^(F05GoodExponent d α)) atTop (𝓝 0) := by
    have hLimit := (((Real.continuous_rpow_const hExponent.le).tendsto 0).comp hZero).const_mul C
    simpa only [Function.comp_def,Real.zero_rpow hExponent.ne',mul_zero] using hLimit
  refine ⟨fun k => F05_good_segment_quotient_holder (hh k) hGood (hSegment k) (hIn k) hHolder,?_⟩
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [(tendsto_order.mp hPower).2 ε hε] with k hk p hp
  rw [dist_eq_norm,norm_sub_rev]
  exact (hError k p hp).trans_lt hk

end Yau.Proofs.F05Aux
