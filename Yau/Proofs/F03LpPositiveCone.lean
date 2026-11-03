import Yau.Proofs.F03ScalarL2

/-! The actual real L² positive cone and its genuine integral duality. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace
namespace Yau.Proofs.F03Aux

variable {α : Type*} [MeasurableSpace α]

theorem lp_inner_nonneg_of_ae_nonneg (ν : Measure α) (f k : Lp ℝ 2 ν)
    (hf : ∀ᵐ x ∂ν, 0 ≤ f x) (hk : ∀ᵐ x ∂ν, 0 ≤ k x) : 0 ≤ inner ℝ f k := by
  rw [L2.inner_def]
  apply integral_nonneg_of_ae
  filter_upwards [hf,hk] with x hx hy
  simpa only [RCLike.inner_apply,conj_trivial,Pi.zero_apply] using mul_nonneg hy hx

theorem lp_inner_negPart (ν : Measure α) (f : Lp ℝ 2 ν) :
    inner ℝ f (Lp.negPart f) = -‖Lp.negPart f‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def,L2.inner_def,← integral_neg]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_negPart f] with x hx
  rw [hx]
  simp only [RCLike.inner_apply,conj_trivial]
  rcases le_total (f x) 0 with hf | hf
  · rw [min_eq_left hf]
    ring
  · rw [min_eq_right hf]
    ring

/-- All genuinely nonnegative L² test vectors detect the actual positive
cone; no abstract positivity assumption on a Riesz representative is needed. -/
theorem lp_nonneg_of_inner_nonneg (ν : Measure α) (f : Lp ℝ 2 ν)
    (h : ∀ k : Lp ℝ 2 ν, (∀ᵐ x ∂ν, 0 ≤ k x) → 0 ≤ inner ℝ f k) :
    ∀ᵐ x ∂ν, 0 ≤ f x := by
  have hn : ∀ᵐ x ∂ν, 0 ≤ Lp.negPart f x := by
    filter_upwards [Lp.coeFn_negPart f] with x hx
    rw [hx]
    exact neg_nonneg.mpr (min_le_right _ _)
  have hi := h (Lp.negPart f) hn
  rw [lp_inner_negPart] at hi
  have hnzero : Lp.negPart f = 0 := by
    apply norm_eq_zero.mp
    nlinarith [norm_nonneg (Lp.negPart f)]
  have hne := Lp.ext_iff.mp hnzero
  filter_upwards [hne,Lp.coeFn_negPart f,Lp.coeFn_zero (E := ℝ) (p := 2) (μ := ν)] with x he hc hzero
  have hm : min (f x) 0 = 0 := neg_eq_zero.mp (hc.symm.trans (he.trans hzero))
  exact min_eq_right_iff.mp hm

end Yau.Proofs.F03Aux
