import Yau.Proofs.F05BootstrapQuotientSource
import Yau.Proofs.F05BootstrapQuotientLimit

/-! The actual shifted current jets converge uniformly from their Holder
bound alone. No joint differentiability of a Hessian is used. -/

open Set Filter
open scoped Topology
noncomputable section
set_option maxHeartbeats 1400000
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux
variable {n : ℕ} {V : Type*} [NormedAddCommGroup V]

theorem F05_good_shift_weight_to_base (d : Option (RIdx n)) {h α : ℝ}
    (hh : 0 ≤ h) (hα : 0 < α) (p : Point n) :
    holderWeight α (F05GoodShift d h p) p ≤ h^(F05GoodExponent d α) := by
  cases d with
  | none =>
    simpa only [F05GoodShift,F05GoodSegment,timeTranslatePoint,zero_mul,add_zero,sub_eq_add_neg] using
      F05_good_segment_weight_to_base (none : Option (RIdx n)) hh hα p (θ := 0) (by norm_num)
  | some j =>
    simpa only [F05GoodShift,F05GoodSegment,spatialTranslatePoint,one_mul] using
      F05_good_segment_weight_to_base (some j) hh hα p (θ := 1) (by norm_num)

theorem F05_good_shifts_uniform_limit {d : Option (RIdx n)} {α C : ℝ}
    (hα : 0 < α) {Q K : Set (Point n)} {f : Point n → V} {h : ℕ → ℝ}
    (hh : ∀ k, 0 ≤ h k) (hZero : Tendsto h atTop (𝓝 0))
    (hQ : Q ⊆ K) (hMap : ∀ k, MapsTo (F05GoodShift d (h k)) Q K)
    (hHolder : HolderBound α K f C) :
    TendstoUniformlyOn (fun k p => f (F05GoodShift d (h k) p)) f atTop Q := by
  have hExponent : 0 < F05GoodExponent d α := by cases d <;> dsimp only [F05GoodExponent] <;> positivity
  have hPower : Tendsto (fun k => C*(h k)^(F05GoodExponent d α)) atTop (𝓝 0) := by
    have hLimit := (((Real.continuous_rpow_const hExponent.le).tendsto 0).comp hZero).const_mul C
    simpa only [Function.comp_def,Real.zero_rpow hExponent.ne',mul_zero] using hLimit
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [(tendsto_order.mp hPower).2 ε hε] with k hk p hp
  rw [dist_eq_norm,norm_sub_rev]
  exact ((hHolder.2.2 _ (hMap k hp) p (hQ hp)).trans
    (mul_le_mul_of_nonneg_left (F05_good_shift_weight_to_base d (hh k) hα p) hHolder.1)).trans_lt hk

end Yau.Proofs.F05Aux
