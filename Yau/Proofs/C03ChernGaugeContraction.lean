import Mathlib

/-! Finite contractions of a computed metric-lowered curvature matrix under
simultaneous changes of holomorphic base coordinates and fibre frame. -/

noncomputable section
open scoped Matrix

namespace Yau.Proofs.C03Aux.ChernGauge

theorem sum_swap_pair_blocks
    {α β γ δ V : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    [AddCommMonoid V] (f : α → β → γ → δ → V) :
    (∑ i, ∑ j, ∑ p, ∑ q, f i j p q) = ∑ p, ∑ q, ∑ i, ∑ j, f i j p q := by
  calc
    _ = ∑ ij : α × β, ∑ pq : γ × δ, f ij.1 ij.2 pq.1 pq.2 := by
      simp only [Fintype.sum_prod_type]
    _ = ∑ pq : γ × δ, ∑ ij : α × β, f ij.1 ij.2 pq.1 pq.2 := Finset.sum_comm
    _ = _ := by simp only [Fintype.sum_prod_type]

def matrixCurvatureQuadratic {n r : ℕ}
    (F : Fin n → Fin n → Matrix (Fin r) (Fin r) ℂ)
    (u : Fin r → ℂ) (a : Fin n → ℂ) : ℂ :=
  star u ⬝ᵥ ((∑ i, ∑ j, (a i * star (a j)) • F i j) *ᵥ u)

theorem matrixCurvatureQuadratic_fourfold {n r : ℕ}
    (F : Fin n → Fin n → Matrix (Fin r) (Fin r) ℂ)
    (u : Fin r → ℂ) (a : Fin n → ℂ) :
    matrixCurvatureQuadratic F u a =
      ∑ α, ∑ β, ∑ i, ∑ j, F i j β α * u α * star (u β) * a i * star (a j) := by
  unfold matrixCurvatureQuadratic
  simp only [dotProduct, Matrix.mulVec, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, Pi.star_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro α _
  apply Finset.sum_congr rfl
  intro β _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem directional_curvature_change {m n r : ℕ}
    (F : Fin n → Fin n → Matrix (Fin r) (Fin r) ℂ)
    (D : Matrix (Fin n) (Fin m) ℂ) (a : Fin m → ℂ) :
    (∑ i, ∑ j, (a i * star (a j)) •
      (∑ p, ∑ q, (D p i * star (D q j)) • F p q)) =
      ∑ p, ∑ q, ((D *ᵥ a) p * star ((D *ᵥ a) q)) • F p q := by
  simp only [Finset.smul_sum, smul_smul]
  rw [sum_swap_pair_blocks]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  simp only [Matrix.mulVec, dotProduct, star_sum, star_mul, Finset.sum_mul,
    Finset.mul_sum, Finset.sum_smul]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  ring

theorem matrixCurvatureQuadratic_gauge {m n r s : ℕ}
    (F : Fin n → Fin n → Matrix (Fin r) (Fin r) ℂ)
    (D : Matrix (Fin n) (Fin m) ℂ) (J : Matrix (Fin r) (Fin s) ℂ)
    (u : Fin s → ℂ) (a : Fin m → ℂ) :
    matrixCurvatureQuadratic
        (fun i j => Jᴴ * (∑ p, ∑ q, (D p i * star (D q j)) • F p q) * J) u a =
      matrixCurvatureQuadratic F (J *ᵥ u) (D *ᵥ a) := by
  have hsum : (∑ i, ∑ j, (a i * star (a j)) •
      (Jᴴ * (∑ p, ∑ q, (D p i * star (D q j)) • F p q) * J)) =
      Jᴴ * (∑ p, ∑ q, ((D *ᵥ a) p * star ((D *ᵥ a) q)) • F p q) * J := by
    calc
      _ = Jᴴ * (∑ i, ∑ j, (a i * star (a j)) •
          (∑ p, ∑ q, (D p i * star (D q j)) • F p q)) * J := by
        simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
      _ = _ := by rw [directional_curvature_change]
  unfold matrixCurvatureQuadratic
  rw [hsum]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.star_mulVec]

end Yau.Proofs.C03Aux.ChernGauge
