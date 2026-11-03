import Yau.Proofs.V04WallErrorContractionFinal
import Yau.Proofs.V04WallErrorAlgebra

/-! Finite sums contracting the three computed Hessian blocks. -/

open scoped Matrix
noncomputable section
namespace Yau.Blueprint.V04Proof.WallErrorAux
open Yau

variable {n : ℕ}

theorem sum_four_pair_swap {ι : Type*} [Fintype ι] (f : ι → ι → ι → ι → ℂ) :
    (∑ i, ∑ j, ∑ a, ∑ b, f i j a b) = ∑ a, ∑ b, ∑ i, ∑ j, f i j a b := by
  calc
    _ = ∑ i, ∑ a, ∑ b, ∑ j, f i j a b := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]

theorem symplecticP_quadratic_contraction
    (W : CotangentMatrix n) (ξ : Fin n → ℂ) (U : Matrix (Fin n) (Fin n) ℂ)
    (M : Fin n → Fin n → Matrix (Fin n) (Fin n) ℂ)
    (B D : Fin n → Matrix (Fin n) (Fin n) ℂ)
    (h11 : ∀ i j, W.toBlocks₁₁ i j = ∑ a, ∑ b, star (ξ a) * M i j b a * ξ b)
    (h22 : ∀ i j, W.toBlocks₂₂ i j = U j i)
    (h12 : ∀ i j, W.toBlocks₁₂ i j = ∑ a, star (ξ a) * B i j a)
    (hBD : ∀ j i b, star (B j i b) = D j b i) :
    symplecticP W =
      (∑ a, ∑ b, star (ξ a) *
        ((∑ i, ∑ j, U j i * M i j b a) -
          ∑ i, ∑ j, B i j a * D j b i) * ξ b).re := by
  have ht : Matrix.trace (W.toBlocks₁₁ * W.toBlocks₂₂ᵀ) =
      ∑ a, ∑ b, star (ξ a) * (∑ i, ∑ j, U j i * M i j b a) * ξ b := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply,
      h11, h22, Finset.sum_mul]
    rw [sum_four_pair_swap]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    simp only [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hc : (∑ i, ∑ j, W.toBlocks₁₂ i j * star (W.toBlocks₁₂ j i)) =
      ∑ a, ∑ b, star (ξ a) * (∑ i, ∑ j, B i j a * D j b i) * ξ b := by
    simp only [h12, star_sum, star_mul, star_star, hBD, Finset.mul_sum, Finset.sum_mul]
    rw [sum_four_pair_swap, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [symplecticP, ht, hc]
  simp only [mul_sub, sub_mul, Finset.sum_sub_distrib]

end Yau.Blueprint.V04Proof.WallErrorAux
