import Yau.Proofs.C05HarnackAlgebra

/-! Exact diagonal-frame cancellation of the scalar Harnack evolution terms. -/

open scoped BigOperators

noncomputable section

namespace Yau.Proofs.C05Aux

variable {n : ℕ}

def diagonalScalarHarnackEvolution (lam : Fin n → ℝ) (k : ℝ)
    (M : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  3 * (∑ i, lam i * ((M - Matrix.diagonal
    (fun i => ((lam i * (lam i + k) : ℝ) : ℂ))) i i).re) +
    2 * (∑ i, lam i ^ 3) + k * (∑ i, lam i ^ 2) - k ^ 2 * (∑ i, lam i)

theorem diagonalScalarHarnackEvolution_eq (lam : Fin n → ℝ) (k : ℝ)
    (M : Matrix (Fin n) (Fin n) ℂ) :
    diagonalScalarHarnackEvolution lam k M =
      -diagonalHarnackPower lam k + 3 * ∑ i, lam i * (M i i).re := by
  have hs :
      (∑ i, (3 * lam i * ((M i i).re - lam i * (lam i + k)) +
        2 * lam i ^ 3 + k * lam i ^ 2 - k ^ 2 * lam i)) =
      ∑ i, (-(lam i * (lam i + k) ^ 2) + 3 * lam i * (M i i).re) := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_neg_distrib,
    mul_assoc, ← Finset.mul_sum] at hs
  simpa [diagonalScalarHarnackEvolution, diagonalHarnackPower] using hs

set_option backward.isDefEq.respectTransparency false in
theorem diagonal_harnack_cancellation (lam : Fin n → ℝ) (hlam : ∀ i, 0 < lam i)
    (k E : ℝ) (M P : Matrix (Fin n) (Fin n) ℂ) :
    diagonalScalarHarnackEvolution lam k M -
      (-weightedHessianSquare lam (M - Matrix.diagonal
        (fun i => ((lam i * (lam i + k) : ℝ) : ℂ))) - weightedHessianSquare lam P + E) =
      weightedHessianSquare lam P + (∑ i, lam i * (M i i).re) -
        2 * k * M.trace.re + weightedHessianSquare lam M - E := by
  have ht : M.trace.re = ∑ i, (M i i).re := by simp [Matrix.trace]
  have hs : (∑ i, (lam i + k) * (M i i).re) =
      (∑ i, lam i * (M i i).re) + k * M.trace.re := by
    rw [ht, Finset.mul_sum]
    simp only [add_mul, Finset.sum_add_distrib]
  rw [diagonalScalarHarnackEvolution_eq, weightedHessianSquare_shift lam hlam k M, hs]
  ring

end Yau.Proofs.C05Aux
