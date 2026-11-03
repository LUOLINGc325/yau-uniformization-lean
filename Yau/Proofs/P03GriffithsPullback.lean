import Yau.LeafProofs.L07

open scoped Matrix

noncomputable section

namespace Yau.NodeProofs.P03Aux

open Yau.BundleDbar

theorem sum_four_swap {α β γ δ A : Type*} [Fintype α] [Fintype β]
    [Fintype γ] [Fintype δ] [AddCommMonoid A] (f : α → β → γ → δ → A) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
  calc
    _ = ∑ a, ∑ c, ∑ b, ∑ d, f a b c d := by
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ b, ∑ d, f a b c d := Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ d, ∑ b, f a b c d := by
      apply Finset.sum_congr rfl
      intro c _
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro c _
      exact Finset.sum_comm

theorem base_contraction_pullback {n m : ℕ}
    (R : Fin n → Fin n → ℂ) (D : Matrix (Fin n) (Fin m) ℂ) (ξ : ComplexVector m) :
    (∑ i, ∑ j, (∑ p, ∑ q, D p i * star (D q j) * R p q) * ξ i * star (ξ j)) =
      ∑ p, ∑ q, R p q * (D *ᵥ fun i => ξ i) p * star ((D *ᵥ fun i => ξ i) q) := by
  simp only [Matrix.mulVec, dotProduct, star_sum, star_mul, Finset.sum_mul, Finset.mul_sum]
  rw [sum_four_swap]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem griffithsQuadratic_base_pullback {n m r : ℕ}
    (R : Fin n → Fin n → Matrix (Fin r) (Fin r) ℂ)
    (D : Matrix (Fin n) (Fin m) ℂ) (ξ : ComplexVector m) (v : ComplexVector r) :
    griffithsQuadratic (fun i j => ∑ p, ∑ q, (D p i * star (D q j)) • R p q) ξ v =
      griffithsQuadratic R (WithLp.toLp 2 (D *ᵥ fun i => ξ i)) v := by
  unfold griffithsQuadratic
  apply congrArg Complex.re
  conv_lhs => rw [sum_four_swap]
  conv_rhs => rw [sum_four_swap]
  apply Finset.sum_congr rfl
  intro α _
  apply Finset.sum_congr rfl
  intro β _
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  have h := congrArg (fun c : ℂ => c * star (v α) * v β)
    (base_contraction_pullback (fun p q => R p q α β) D ξ)
  simpa only [Finset.sum_mul] using h

end Yau.NodeProofs.P03Aux
