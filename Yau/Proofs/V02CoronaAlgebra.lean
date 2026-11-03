import Yau.Proofs.V02Minors

/-! Finite algebra of the skew-symmetric corona correction. All identities
hold even when individual minors vanish. -/

open scoped Matrix ComplexOrder
open Finset

noncomputable section
namespace Yau.Blueprint.V02Proof

variable {ι κ β : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] [Fintype β] [DecidableEq β]

theorem skew_quadratic_sum_zero (Q : Matrix ι ι ℂ)
    (hQ : ∀ i j, Q i j = -Q j i) (a : ι → ℂ) :
    ∑ i, (∑ j, Q i j * a j) * a i = 0 := by
  let s : ℂ := ∑ i, (∑ j, Q i j * a j) * a i
  have hs : s = -s := by
    dsimp only [s]
    simp only [sum_mul, ← sum_neg_distrib]
    rw [sum_comm]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    rw [hQ j i]
    ring
  change s = 0
  linear_combination (1 / 2 : ℂ) * hs

theorem corona_sum_eq_one (a σ : ι → ℂ) (Q : Matrix ι ι ℂ)
    (hσ : ∑ i, σ i * a i = 1) (hQ : ∀ i j, Q i j = -Q j i) :
    ∑ i, (σ i + ∑ j, Q i j * a j) * a i = 1 := by
  simp only [add_mul, sum_add_distrib]
  rw [hσ, skew_quadratic_sum_zero Q hQ a, add_zero]

/-- The exact algebra after taking one antiholomorphic derivative. -/
theorem corona_dbar_correction_zero (a σ dσ : ι → ℂ)
    (hσ : ∑ i, σ i * a i = 1) (hdσ : ∑ i, dσ i * a i = 0) (i : ι) :
    dσ i + ∑ j, (σ i * dσ j - σ j * dσ i) * a j = 0 := by
  simp only [sub_mul, sum_sub_distrib]
  have h₁ : ∑ j, σ i * dσ j * a j = σ i * ∑ j, dσ j * a j := by
    simp only [mul_sum, mul_assoc]
  have h₂ : ∑ j, σ j * dσ i * a j = dσ i * ∑ j, σ j * a j := by
    simp only [mul_sum]
    apply sum_congr rfl
    intro j _
    ring
  rw [h₁, h₂, hdσ, hσ]
  ring

/-- The corrected scalar coefficients combine the individual Cramer solutions. -/
theorem combine_cramer_coefficients {Λ : Type*} [Fintype Λ]
    (A : Matrix κ β ℂ) (Y : κ → ℂ) (a g : Λ → ℂ) (c : Λ → β → ℂ)
    (hc : ∀ k, A *ᵥ c k = a k • Y) (hg : ∑ k, g k * a k = 1)
    (α : ℂ) :
    A *ᵥ (∑ k, (α * g k) • c k) = α • Y := by
  simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, hc, smul_smul]
  rw [← Finset.sum_smul]
  congr 1
  calc
    (∑ k, α * g k * a k) = α * ∑ k, g k * a k := by
      simp only [mul_sum, mul_assoc]
    _ = α := by rw [hg, mul_one]

end Yau.Blueprint.V02Proof
