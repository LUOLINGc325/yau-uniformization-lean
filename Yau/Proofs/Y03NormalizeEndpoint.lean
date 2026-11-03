import Yau.Proofs.Y03EndpointForms

/-! Normalize the right endpoint in its actual singular frame. -/

open scoped Matrix

noncomputable section

namespace Yau.Blueprint.Alignment.Y03Proof

open Yau

variable {n : ℕ}

theorem matrixForm_conjugate (A B : Herm n) (v : Fin n → ℂ) :
    matrixForm A (B *ᵥ v) = matrixForm (B.conjTranspose * A * B) v := by
  exact congrArg Complex.re (conjugate_quadratic A B v)

theorem real_diagonal_conjTranspose (d : Fin n → ℝ) :
    (Matrix.diagonal (fun i => (d i : ℂ))).conjTranspose = Matrix.diagonal (fun i => (d i : ℂ)) := by
  ext i j
  by_cases hij : i = j
  · subst j; simp [Matrix.conjTranspose_apply]
  · simp [Matrix.conjTranspose_apply, hij, Ne.symm hij]

def endpointDiagonal (μ : Fin n → ℝ) (T : ℝ) : Herm n :=
  Matrix.diagonal (fun i => (Real.exp (-μ i * T / 2) : ℂ))

theorem endpointDiagonal_sq (μ : Fin n → ℝ) (T : ℝ) :
    endpointDiagonal μ T * endpointDiagonal μ T =
      Matrix.diagonal (fun i => (Real.exp (-μ i * T) : ℂ)) := by
  unfold endpointDiagonal
  rw [Matrix.diagonal_mul_diagonal]
  apply congrArg Matrix.diagonal
  funext i
  rw [← Complex.ofReal_mul, ← Real.exp_add]
  congr 2
  ring

theorem endpointDiagonal_inverse_cancellation (μ : Fin n → ℝ) (T : ℝ) :
    endpointDiagonal μ T * Matrix.diagonal (fun i => (Real.exp (μ i * T) : ℂ)) *
      endpointDiagonal μ T = 1 := by
  unfold endpointDiagonal
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  apply congrArg Matrix.diagonal
  funext i
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Real.exp_add, ← Real.exp_add]
  have hz : -μ i * T / 2 + μ i * T + -μ i * T / 2 = 0 := by ring
  rw [hz, Real.exp_zero, Complex.ofReal_one]

theorem right_endpoint_form_normalization (μ : Fin n → ℝ) (T : ℝ) (A : Herm n)
    (hbound : ∀ v : Fin n → ℂ,
      (∑ i, μ i * Real.exp (μ i * T) * ‖v i‖ ^ 2) ≤
        matrixForm (Matrix.diagonal (fun i => (Real.exp (μ i * T) : ℂ)) *
          (endpointDiagonal μ T * A * endpointDiagonal μ T) *
          Matrix.diagonal (fun i => (Real.exp (μ i * T) : ℂ))) v)
    (v : Fin n → ℂ) : (∑ i, μ i * ‖v i‖ ^ 2) ≤ matrixForm A v := by
  let D := endpointDiagonal μ T
  let K : Herm n := Matrix.diagonal (fun i => (Real.exp (μ i * T) : ℂ))
  have hDstar : D.conjTranspose = D := real_diagonal_conjTranspose _
  have hcancel : D * K * D = 1 := endpointDiagonal_inverse_cancellation μ T
  have hquad : matrixForm (K * (D * A * D) * K) (D *ᵥ v) = matrixForm A v := by
    rw [matrixForm_conjugate, hDstar]
    have hmat : D * (K * (D * A * D) * K) * D = A := by
      calc
        _ = (D * K * D) * A * (D * K * D) := by noncomm_ring
        _ = A := by rw [hcancel, Matrix.one_mul, Matrix.mul_one]
    rw [hmat]
  have hnorm (i : Fin n) : Real.exp (μ i * T) * ‖(D *ᵥ v) i‖ ^ 2 = ‖v i‖ ^ 2 := by
    change Real.exp (μ i * T) * ‖(Matrix.diagonal (fun j => (Real.exp (-μ j * T / 2) : ℂ)) *ᵥ v) i‖ ^ 2 = _
    rw [Matrix.mulVec_diagonal, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), mul_pow, pow_two (Real.exp _)]
    rw [← mul_assoc, ← Real.exp_add, ← Real.exp_add]
    have hz : μ i * T + (-μ i * T / 2 + -μ i * T / 2) = 0 := by ring
    rw [hz, Real.exp_zero, one_mul]
  have hb := hbound (D *ᵥ v)
  change (∑ i, μ i * Real.exp (μ i * T) * ‖(D *ᵥ v) i‖ ^ 2) ≤
    matrixForm (K * (D * A * D) * K) (D *ᵥ v) at hb
  rw [hquad] at hb
  simpa only [mul_assoc, hnorm] using hb

end Yau.Blueprint.Alignment.Y03Proof
