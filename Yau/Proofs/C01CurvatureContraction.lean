import Yau.Proofs.C01SpatialLineJets

/-! Finite matrix identities identifying the curvature of an actual spatial
line with the original four-index bisectional contraction. -/

noncomputable section

open scoped Matrix

namespace Yau.NodeProofs.C01Aux

open Yau Yau.Blueprint

variable {n : ℕ}

theorem curvature_direction_matrix (K : Herm n)
    (A B : Fin n → Herm n) (D : Fin n → Fin n → Herm n) (d : Fin n → ℂ) :
    -(∑ k, ∑ l, (d k * star (d l)) • D k l) +
        (∑ l, star (d l) • B l) * K * (∑ k, d k • A k) =
      ∑ k, ∑ l, (d k * star (d l)) • (-D k l + B l * K * A k) := by
  have hp : (∑ l, star (d l) • B l) * K * (∑ k, d k • A k) =
      ∑ k, ∑ l, (d k * star (d l)) • (B l * K * A k) := by
    simp only [Finset.mul_sum, Finset.sum_mul, smul_mul_assoc,
      mul_smul_comm, Finset.smul_sum, smul_smul]
  rw [hp]
  simp only [smul_add, smul_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib]

theorem curvature_direction_entry (K : Herm n)
    (A B : Fin n → Herm n) (D : Fin n → Fin n → Herm n)
    (d : Fin n → ℂ) (a b : Fin n) :
    (-(∑ k, ∑ l, (d k * star (d l)) • D k l) +
        (∑ l, star (d l) • B l) * K * (∑ k, d k • A k)) a b =
      ∑ k, ∑ l, d k * star (d l) *
        (-D k l a b + ∑ p, ∑ q, K p q * A k q b * B l a p) := by
  rw [curvature_direction_matrix]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.add_apply, Matrix.neg_apply]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  congr 2
  simp only [Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  ring

theorem curvature_direction_contraction (K : Herm n)
    (A B : Fin n → Herm n) (D : Fin n → Fin n → Herm n)
    (d ξ : Fin n → ℂ) :
    star ξ ⬝ᵥ ((-(∑ k, ∑ l, (d k * star (d l)) • D k l) +
        (∑ l, star (d l) • B l) * K * (∑ k, d k • A k)) *ᵥ ξ) =
      ∑ i, ∑ j, ∑ k, ∑ l,
        (-D k l j i + ∑ p, ∑ q, K p q * A k q i * B l j p) *
          ξ i * star (ξ j) * d k * star (d l) := by
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply]
  simp_rw [curvature_direction_entry]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

end Yau.NodeProofs.C01Aux
