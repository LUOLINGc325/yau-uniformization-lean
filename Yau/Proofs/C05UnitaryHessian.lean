import Yau.Proofs.C05PositiveTrace
import Yau.Proofs.C05PureHessianBound

/-! The mixed/pure complex Hessian decomposition is strictly negative once
the scalar trace error and the weighted pure square are small. -/

noncomputable section
open scoped BigOperators ComplexOrder

namespace Yau.Proofs.C05Aux
open Matrix
variable {n : ℕ}

theorem real_diagonal_quadratic (d : Fin n → ℝ) (v : Fin n → ℂ) :
    (star v ⬝ᵥ (Matrix.diagonal (fun i => (d i : ℂ)) *ᵥ v)).re =
      ∑ i, d i * ‖v i‖ ^ 2 := by
  simp only [dotProduct, Matrix.mulVec_diagonal]
  change Complex.reCLM (∑ i, star (v i) * ((d i : ℂ) * v i)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  change (star (v i) * ((d i : ℂ) * v i)).re = d i * ‖v i‖ ^ 2
  simp only [Pi.star_apply, Pi.mul_apply, Complex.star_def, Complex.mul_re,
    Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, Complex.sq_norm, Complex.normSq_apply]
  ring

theorem positive_quadratic_le_trace (M : Matrix (Fin n) (Fin n) ℂ) (hM : M.PosSemidef)
    (v : Fin n → ℂ) : (star v ⬝ᵥ (M *ᵥ v)).re ≤ M.trace.re * (∑ i, ‖v i‖ ^ 2) := by
  have he : (M.trace.re : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) =
      Matrix.diagonal (fun _ => (M.trace.re : ℂ)) := by
    ext i j
    by_cases hij : i = j <;> simp [hij, Matrix.diagonal]
  have hp := (Complex.nonneg_iff.mp ((positive_matrix_le_trace M hM).dotProduct_mulVec_nonneg v)).1
  rw [he] at hp
  simp only [Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re] at hp
  rw [real_diagonal_quadratic, ← Finset.mul_sum] at hp
  linarith

def unitaryHessianQuadratic (H P : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) : ℝ :=
  2 * (star v ⬝ᵥ (H *ᵥ v)).re + 2 * (∑ i, ∑ j, P i j * v i * v j).re

theorem unitaryHessianQuadratic_le (lam : Fin n → ℝ) (hlam : ∀ i, 0 < lam i)
    {a L k : ℝ} (ha : 0 ≤ a) (hlow : ∀ i, a ≤ lam i) (hup : ∀ i, lam i ≤ L)
    (hk : 0 ≤ k) (M : Matrix (Fin n) (Fin n) ℂ) (hM : M.PosSemidef)
    (P : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) :
    unitaryHessianQuadratic
        (M - Matrix.diagonal (fun i => ((lam i * (lam i + k) : ℝ) : ℂ))) P v ≤
      (M.trace.re - a ^ 2 + (n : ℝ) * Real.sqrt (L * weightedHessianSquare lam P)) *
        (2 * ∑ i, ‖v i‖ ^ 2) := by
  have hm := positive_quadratic_le_trace M hM v
  have hd : a ^ 2 * (∑ i, ‖v i‖ ^ 2) ≤
      ∑ i, (lam i * (lam i + k)) * ‖v i‖ ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    nlinarith [hlow i, hlam i, mul_nonneg (hlam i).le hk]
  have hp := (Complex.re_le_norm (∑ i, ∑ j, P i j * v i * v j)).trans
    (pure_quadratic_le_weighted_square lam hlam hup P v)
  unfold unitaryHessianQuadratic
  simp only [Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re, real_diagonal_quadratic]
  nlinarith

theorem unitaryHessianQuadratic_negative (lam : Fin n → ℝ) (hlam : ∀ i, 0 < lam i)
    {a L k : ℝ} (ha : 0 ≤ a) (hlow : ∀ i, a ≤ lam i) (hup : ∀ i, lam i ≤ L)
    (hk : 0 ≤ k) (M : Matrix (Fin n) (Fin n) ℂ) (hM : M.PosSemidef)
    (P : Matrix (Fin n) (Fin n) ℂ)
    (hsmall : M.trace.re + (n : ℝ) * Real.sqrt (L * weightedHessianSquare lam P) ≤ a ^ 2 / 2)
    (v : Fin n → ℂ) :
    unitaryHessianQuadratic
        (M - Matrix.diagonal (fun i => ((lam i * (lam i + k) : ℝ) : ℂ))) P v ≤
      -(a ^ 2 / 2) * (2 * ∑ i, ‖v i‖ ^ 2) := by
  apply (unitaryHessianQuadratic_le lam hlam ha hlow hup hk M hM P v).trans
  apply mul_le_mul_of_nonneg_right (by linarith)
  positivity

end Yau.Proofs.C05Aux
