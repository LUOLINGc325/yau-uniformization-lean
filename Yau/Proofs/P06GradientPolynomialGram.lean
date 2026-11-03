import Yau.LeafProofs.L23TensorCalculus

noncomputable section
open scoped InnerProductSpace

namespace Yau.NodeProofs.P06Aux.GradientPoly

variable {ι κ E : Type*} [Fintype ι] [Fintype κ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A finite Gram factor computes the full metric contraction, including
all cross terms, as a sum of genuine directional squared norms. -/
theorem gram_inner_eq_sum_norm_sq (H : Matrix ι ι ℝ) (F : Matrix ι κ ℝ)
    (hF : H = F * F.transpose) (V : ι → E) :
    (∑ a, ∑ b, H a b * inner ℝ (V a) (V b)) =
      ∑ s, ‖∑ a, F a s • V a‖ ^ 2 := by
  classical
  simp only [← real_inner_self_eq_norm_sq, inner_sum, sum_inner,
    real_inner_smul_left, real_inner_smul_right, hF,
    Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  conv_lhs =>
    arg 2
    ext a
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [real_inner_comm (V a) (V b)]
  ring

/-- Directionwise contraction after arbitrary real combinations implies
contraction of every positive definite inverse-metric Gram sum. -/
theorem inverse_metric_gram_contraction [DecidableEq ι]
    (G : Matrix ι ι ℝ) (hG : G.PosDef) (V W : ι → E)
    (h : ∀ c : ι → ℝ, ‖∑ a, c a • W a‖ ^ 2 ≤ ‖∑ a, c a • V a‖ ^ 2) :
    (∑ a, ∑ b, G⁻¹ a b * inner ℝ (W a) (W b)) ≤
      ∑ a, ∑ b, G⁻¹ a b * inner ℝ (V a) (V b) := by
  obtain ⟨F, hF⟩ := Yau.LeafProofs.L23Aux.inverseMetric_exists_gram_factor G hG
  rw [gram_inner_eq_sum_norm_sq _ F hF, gram_inner_eq_sum_norm_sq _ F hF]
  exact Finset.sum_le_sum (fun s _ => h (fun a => F a s))

end Yau.NodeProofs.P06Aux.GradientPoly
