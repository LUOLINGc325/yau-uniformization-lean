import Yau.Proofs.E01Matrix

/-! The finite Chern tensor contraction with the paper's inverse-transpose convention. -/

noncomputable section
open scoped Matrix

namespace Yau.NodeProofs.E01Aux
open Yau Yau.Blueprint

variable {n : ℕ}

theorem chern_residual_entry (G A C M : Herm n) (i j : Fin n) :
    (Aᵀ * Gᵀ * Cᵀ - Mᵀ) i j =
      -M j i + ∑ p, ∑ q, G p q * A q i * C j p := by
  simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  have hh : (∑ p, ∑ q, A q i * G p q * C j p) =
      ∑ p, ∑ q, G p q * A q i * C j p := by
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro q _
    ring
  rw [hh]
  ring

theorem chern_residual_direction_sum
    (G : Herm n) (A C : Fin n → Herm n) (M : Fin n → Fin n → Herm n)
    (a : Fin n → ℂ) :
    (∑ k, a k • A k)ᵀ * Gᵀ * (∑ l, star (a l) • C l)ᵀ -
        (∑ k, ∑ l, (a k * star (a l)) • M k l)ᵀ =
      ∑ k, ∑ l, (a k * star (a l)) • ((A k)ᵀ * Gᵀ * (C l)ᵀ - (M k l)ᵀ) := by
  simp only [Matrix.transpose_sum, Matrix.transpose_smul, Matrix.sum_mul, Matrix.mul_sum,
    Matrix.smul_mul, Matrix.mul_smul, Finset.smul_sum, smul_smul, smul_sub, Finset.sum_sub_distrib]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  rw [mul_comm]

end Yau.NodeProofs.E01Aux
