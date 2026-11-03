import Yau.Proofs.Y03NormalizeEndpoint
import Yau.Proofs.Y03Weights
import Yau.Proofs.Y03Grid
import Yau.Proofs.Y03Inverse

/-! Strict propagated-weight support gives the exact exponential diagonal conjugation gain. -/

open scoped Matrix

noncomputable section

namespace Yau.Blueprint.Alignment.Y03Proof

open Yau

variable {n : ℕ}

theorem weight_within_step_mono (Q : ℕ → ℝ) (N : ℕ) (M hm scale K eps : ℝ)
    (j₀ : ℕ) (μ : ℕ → Fin n → ℝ) (k : ℕ) (i l : Fin n)
    (hpass : μ k l - eps * theta Q (macroAt Q N M hm j₀ k) ≤ μ k i) :
    weight Q N M hm scale K eps j₀ μ k l ≤ weight Q N M hm scale K eps j₀ μ k i := by
  apply propagatedWeight_mono_of_passage
  · exact Finset.mem_product.2 ⟨Finset.mem_range.2 (slotAt_lt_pieces Q N M hm j₀ k), Finset.mem_univ _⟩
  · exact Finset.mem_product.2 ⟨Finset.mem_range.2 (slotAt_lt_pieces Q N M hm j₀ k), Finset.mem_univ _⟩
  · refine ⟨Or.inl rfl, ?_⟩
    simpa only [offset_add_slotAt] using hpass

theorem strict_weight_support_rate_gap (Q : ℕ → ℝ) (N : ℕ) (M hm scale K eps : ℝ)
    (j₀ : ℕ) (μ : ℕ → Fin n → ℝ) (k : ℕ) (L : Herm n)
    (hsupport : ∀ i l, i ≠ l → L i l ≠ 0 →
      weight Q N M hm scale K eps j₀ μ k i < weight Q N M hm scale K eps j₀ μ k l)
    (i l : Fin n) (hil : i ≠ l) (hL : L i l ≠ 0) :
    eps * theta Q (macroAt Q N M hm j₀ k) < μ k l - μ k i := by
  by_contra hn
  have hpass : μ k l - eps * theta Q (macroAt Q N M hm j₀ k) ≤ μ k i := by linarith
  exact (not_le_of_gt (hsupport i l hil hL))
    (weight_within_step_mono Q N M hm scale K eps j₀ μ k i l hpass)

theorem endpointDiagonal_inv (μ : Fin n → ℝ) (T : ℝ) :
    (endpointDiagonal μ T)⁻¹ = Matrix.diagonal (fun i => (Real.exp (μ i * T / 2) : ℂ)) := by
  apply Matrix.inv_eq_left_inv
  unfold endpointDiagonal
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  apply congrArg Matrix.diagonal
  funext i
  rw [← Complex.ofReal_mul, ← Real.exp_add]
  have hz : μ i * T / 2 + -μ i * T / 2 = 0 := by ring
  rw [hz, Real.exp_zero, Complex.ofReal_one]

theorem endpointDiagonal_isUnit (μ : Fin n → ℝ) (T : ℝ) : IsUnit (endpointDiagonal μ T) := by
  apply (Matrix.isUnit_iff_isUnit_det _).2
  unfold endpointDiagonal
  rw [Matrix.det_diagonal]
  exact isUnit_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun i _ =>
    Complex.ofReal_ne_zero.2 (ne_of_gt (Real.exp_pos _)))

theorem endpointDiagonal_conjugate_entry (μ : Fin n → ℝ) (T : ℝ) (L : Herm n) (i l : Fin n) :
    ((endpointDiagonal μ T)⁻¹ * L * endpointDiagonal μ T) i l =
      L i l * (Real.exp (-(μ l - μ i) * T / 2) : ℂ) := by
  rw [endpointDiagonal_inv]
  simp only [endpointDiagonal, Matrix.diagonal_mul, Matrix.mul_diagonal]
  rw [mul_comm (Real.exp (μ i * T / 2) : ℂ) (L i l), mul_assoc,
    ← Complex.ofReal_mul, ← Real.exp_add]
  have heq : μ i * T / 2 + -μ l * T / 2 = -(μ l - μ i) * T / 2 := by ring
  rw [heq]

theorem diagonal_change_identity (D L : Herm n) (hD : IsUnit D) (hL : IsUnit L) :
    L * D * (D⁻¹ * L * D)⁻¹ = D := by
  obtain ⟨_⟩ := hD.nonempty_invertible
  obtain ⟨_⟩ := hL.nonempty_invertible
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.inv_inv_of_invertible]
  calc
    _ = L * (D * D⁻¹) * L⁻¹ * D := by noncomm_ring
    _ = D := by rw [Matrix.mul_inv_of_invertible, Matrix.mul_one,
      Matrix.mul_inv_of_invertible, Matrix.one_mul]

end Yau.Blueprint.Alignment.Y03Proof
