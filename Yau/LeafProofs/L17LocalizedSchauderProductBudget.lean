import Yau.LeafProofs.L17LocalizedSchauderCutoffDifference

open Set
open scoped ContDiff
noncomputable section
namespace Yau.LeafProofs.L17LocalizedSchauderAux

variable {E F G H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Multiplication of an actual cutoff jet and an actual source jet keeps
the source amplitude linear. -/
theorem norm_iteratedFDeriv_product_sub_le_factored (k : ℕ) (B : F →L[ℝ] G →L[ℝ] H)
    {U : Set E} (hU : IsOpen U) (f : E → F) (g₁ g₂ : E → G)
    (hf : ContDiffOn ℝ (k : ℕ∞ω) f U)
    (hg₁ : ContDiffOn ℝ (k : ℕ∞ω) g₁ U) (hg₂ : ContDiffOn ℝ (k : ℕ∞ω) g₂ U)
    {x y : E} (hx : x ∈ U) (hy : y ∈ U) {C K A d : ℝ}
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hA : 0 ≤ A) (hd : 0 ≤ d)
    (hCutoff : ∀ j, j ≤ k → ‖iteratedFDeriv ℝ j f x‖ ≤ C)
    (hSource : ∀ j, j ≤ k → ‖iteratedFDeriv ℝ j g₂ y‖ ≤ K*A)
    (hCutoffDelta : ∀ j, j ≤ k →
      ‖iteratedFDeriv ℝ j f x-iteratedFDeriv ℝ j f y‖ ≤ C*d)
    (hSourceDelta : ∀ j, j ≤ k →
      ‖iteratedFDeriv ℝ j g₁ x-iteratedFDeriv ℝ j g₂ y‖ ≤ K*A*d) :
    ‖iteratedFDeriv ℝ k (fun z => B (f z) (g₁ z)) x-
      iteratedFDeriv ℝ k (fun z => B (f z) (g₂ z)) y‖ ≤
      (2*‖B‖*bilinearJetConstant k*C*K)*A*d := by
  have h := norm_iteratedFDeriv_bilinear_sub_le k B hU f f g₁ g₂ hf hf hg₁ hg₂ hx hy
    hC (mul_nonneg hK hA) (mul_nonneg hC hd) (mul_nonneg (mul_nonneg hK hA) hd)
    hCutoff hSource hCutoffDelta hSourceDelta
  exact h.trans_eq (by ring)

theorem bilinearJetConstant_le_four {k : ℕ} (hk : k ≤ 2) : bilinearJetConstant k ≤ 4 := by
  interval_cases k <;> norm_num [bilinearJetConstant,Finset.sum_range_succ]

end Yau.LeafProofs.L17LocalizedSchauderAux
