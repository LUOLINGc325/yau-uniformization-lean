import Yau.Proofs.F04BanachBilinear

open Filter

noncomputable section

namespace Yau.F04Proof

/-- The constructed extension retains the product estimate for all actual
 completed arguments. -/
theorem bounded_bilinear_extension_pointwise {E V F : Type*}
    [AddCommGroup E] [Module ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (e : E →ₗ[ℝ] V) (he : DenseRange e) (b : E →ₗ[ℝ] E →ₗ[ℝ] F)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ u v, ‖b u v‖ ≤ C * ‖e u‖ * ‖e v‖) :
    ∃ B : V →L[ℝ] V →L[ℝ] F,
      (∀ u v, ‖B u v‖ ≤ C * ‖u‖ * ‖v‖) ∧ ∀ u v, B (e u) (e v) = b u v := by
  obtain ⟨B, hB, hBe⟩ := bounded_bilinear_extension_banach e he b hC hb
  refine ⟨B, ?_, hBe⟩
  intro u v
  exact (B.le_opNorm₂ u v).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hB (norm_nonneg _)) (norm_nonneg _))

end Yau.F04Proof
