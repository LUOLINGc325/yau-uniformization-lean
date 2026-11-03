import Yau.Proofs.D02RelativeSpectrum

/-! The relative spectral product bound is an actual quadratic-form
bound for the original positive Hermitian metric and Gram matrices. -/

open scoped Matrix ComplexOrder

noncomputable section
namespace Yau.NodeProofs.D02Aux
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

theorem matrix_quadratic_congruence (A E : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) :
    star (E *ᵥ v) ⬝ᵥ (A *ᵥ (E *ᵥ v)) = star v ⬝ᵥ ((Eᴴ * A * E) *ᵥ v) := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

theorem matrix_diagonal_quadratic_re (lam : Fin n → ℝ) (v : Fin n → ℂ) :
    (star v ⬝ᵥ (Matrix.diagonal (fun i => (lam i : ℂ)) *ᵥ v)).re =
      ∑ i, lam i * Complex.normSq (v i) := by
  simp only [dotProduct, Complex.re_sum, Pi.star_apply, Matrix.mulVec_diagonal]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.normSq_apply]
  ring

theorem relative_frame_quadratics (H G E : Matrix (Fin n) (Fin n) ℂ) (lam : Fin n → ℝ)
    (hE : Eᴴ * H * E = 1) (hG : Eᴴ * G * E = Matrix.diagonal (fun i => (lam i : ℂ)))
    (v : Fin n → ℂ) :
    (star (E *ᵥ v) ⬝ᵥ (H *ᵥ (E *ᵥ v))).re = ∑ i, Complex.normSq (v i) ∧
      (star (E *ᵥ v) ⬝ᵥ (G *ᵥ (E *ᵥ v))).re = ∑ i, lam i * Complex.normSq (v i) := by
  constructor
  · rw [matrix_quadratic_congruence, hE]
    have h := matrix_diagonal_quadratic_re (fun _ : Fin n => (1 : ℝ)) v
    simpa only [Complex.ofReal_one, Matrix.diagonal_one, one_mul] using h
  · rw [matrix_quadratic_congruence, hG, matrix_diagonal_quadratic_re]

/-- Every vector satisfies the inverse-Jacobian estimate. The trace and
determinant quotient are computed from these same H and G. -/
theorem relative_gram_quadratic_bound (H G : Matrix (Fin n) (Fin n) ℂ)
    (hH : H.PosDef) (hG : G.PosDef) (B : ℝ) (htrace : (H⁻¹ * G).trace.re ≤ B)
    (v : Fin n → ℂ) :
    (star v ⬝ᵥ (H *ᵥ v)).re ≤
      max 1 B ^ (n - 1) / (G.det.re / H.det.re) * (star v ⬝ᵥ (G *ᵥ v)).re := by
  obtain ⟨E, lam, hE, hdiag, hInv, hlam, hTr, hDet⟩ := exists_relative_spectral_data H G hH hG
  have hsurj : Function.Surjective E.mulVec := Matrix.mulVec_surjective_iff_isUnit.mpr
    (Matrix.mulVec_injective_iff_isUnit.mp (relative_frame_mulVec_injective H E hE))
  obtain ⟨w, rfl⟩ := hsurj v
  obtain ⟨hHq, hGq⟩ := relative_frame_quadratics H G E lam hE hdiag w
  rw [hHq, hGq, hDet]
  apply spectral_inverse_bound lam (fun i => Complex.normSq (w i)) hlam
    (fun i => Complex.normSq_nonneg (w i)) B
  rwa [hTr] at htrace

end Yau.NodeProofs.D02Aux
