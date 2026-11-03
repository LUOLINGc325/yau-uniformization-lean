import Yau.LeafProofs.L17LocalizedSchauderCompositionBounds

open Set
open scoped ContDiff
noncomputable section
namespace Yau.LeafProofs.L17LocalizedSchauderAux
open Yau.LeafProofs.L17Aux

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The finite composition budget is uniform over the requested finite orders. -/
def compositionJetBudget (k : ℕ) (D gamma : ℝ) : ℝ :=
  1+∑ j ∈ Finset.range (k+1),
    (taylorOuterDifferenceConstant j D+
      taylorInnerDifferenceConstant j D*D+taylorOuterDifferenceConstant j D*D^gamma)

theorem compositionJetBudget_pos (k : ℕ) {D gamma : ℝ} (hD : 0 ≤ D) :
    0 < compositionJetBudget k D gamma := by
  have hh : 0 ≤ ∑ j ∈ Finset.range (k+1),
      (taylorOuterDifferenceConstant j D+
        taylorInnerDifferenceConstant j D*D+taylorOuterDifferenceConstant j D*D^gamma) :=
    Finset.sum_nonneg (fun j _ => add_nonneg
      (add_nonneg (taylorOuterDifferenceConstant_nonneg j hD)
        (mul_nonneg (taylorInnerDifferenceConstant_nonneg j hD) hD))
      (mul_nonneg (taylorOuterDifferenceConstant_nonneg j hD) (Real.rpow_nonneg hD _)))
  exact add_pos_of_pos_of_nonneg zero_lt_one hh

theorem compositionJetBudget_order_le {k j : ℕ} {D gamma : ℝ} (hD : 0 ≤ D) (hj : j ≤ k) :
    taylorOuterDifferenceConstant j D ≤ compositionJetBudget k D gamma ∧
    taylorInnerDifferenceConstant j D*D+taylorOuterDifferenceConstant j D*D^gamma ≤
      compositionJetBudget k D gamma := by
  have hTerm (i : ℕ) : 0 ≤ taylorOuterDifferenceConstant i D+
      taylorInnerDifferenceConstant i D*D+taylorOuterDifferenceConstant i D*D^gamma :=
    add_nonneg (add_nonneg (taylorOuterDifferenceConstant_nonneg i hD)
      (mul_nonneg (taylorInnerDifferenceConstant_nonneg i hD) hD))
      (mul_nonneg (taylorOuterDifferenceConstant_nonneg i hD) (Real.rpow_nonneg hD _))
  have hOne := Finset.single_le_sum (fun i _ => hTerm i)
    (show j ∈ Finset.range (k+1) from Finset.mem_range.mpr (by omega))
  have hKI := mul_nonneg (taylorInnerDifferenceConstant_nonneg j hD) hD
  have hKO := taylorOuterDifferenceConstant_nonneg j hD
  have hPow := mul_nonneg hKO (Real.rpow_nonneg hD gamma)
  dsimp only [compositionJetBudget]
  constructor <;> linarith

/-- Actual finite jet differences of compositions, with the source amplitude
factored once. The hypotheses are pointwise jets of the two local functions. -/
theorem norm_iteratedFDeriv_comp_sub_le_factored
    {f₁ f₂ : E → F} {g₁ g₂ : F → G} {x y : E} (k j : ℕ) (hj : j ≤ k)
    (hg₁ : ContDiffAt ℝ (j : ℕ∞ω) g₁ (f₁ x))
    (hg₂ : ContDiffAt ℝ (j : ℕ∞ω) g₂ (f₂ y))
    (hf₁ : ContDiffAt ℝ (j : ℕ∞ω) f₁ x)
    (hf₂ : ContDiffAt ℝ (j : ℕ∞ω) f₂ y)
    {A D d gamma : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D) (hd : 0 ≤ d)
    (hOuter : ∀ i, i ≤ j → ‖iteratedFDeriv ℝ i g₁ (f₁ x)‖ ≤ A)
    (hOuterDelta : ∀ i, i ≤ j →
      ‖iteratedFDeriv ℝ i g₁ (f₁ x)-iteratedFDeriv ℝ i g₂ (f₂ y)‖ ≤ A*D^gamma*d)
    (hInner₁ : ∀ i, i ≤ j → ‖iteratedFDeriv ℝ i f₁ x‖ ≤ D)
    (hInner₂ : ∀ i, i ≤ j → ‖iteratedFDeriv ℝ i f₂ y‖ ≤ D)
    (hInnerDelta : ∀ i, i ≤ j →
      ‖iteratedFDeriv ℝ i f₁ x-iteratedFDeriv ℝ i f₂ y‖ ≤ D*d) :
    ‖iteratedFDeriv ℝ j (g₁ ∘ f₁) x-iteratedFDeriv ℝ j (g₂ ∘ f₂) y‖ ≤
      compositionJetBudget k D gamma*A*d := by
  have h := norm_iteratedFDeriv_comp_sub_le j hg₁ hg₂ hf₁ hf₂ hA
    (mul_nonneg (mul_nonneg hA (Real.rpow_nonneg hD gamma)) hd) hD (mul_nonneg hD hd)
    hOuter hOuterDelta hInner₁ hInner₂ hInnerDelta
  calc
    _ ≤ taylorInnerDifferenceConstant j D*A*(D*d)+
        taylorOuterDifferenceConstant j D*(A*D^gamma*d) := h
    _ = (taylorInnerDifferenceConstant j D*D+taylorOuterDifferenceConstant j D*D^gamma)*A*d := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (compositionJetBudget_order_le hD hj).2 hA) hd

end Yau.LeafProofs.L17LocalizedSchauderAux
