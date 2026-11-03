import Yau.Proofs.P06WeitzenbockEigenframe
import Yau.Proofs.D02SpectralProduct

/-! Relative spectral data for the actual metric and immersion Gram
matrices. Every diagonalizer is produced by the accepted pointwise
Hermitian spectral theorem, including in dimension zero. -/

open scoped Matrix ComplexOrder

noncomputable section
namespace Yau.NodeProofs.D02Aux
open Yau
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

theorem relative_frame_mulVec_injective (H E : Matrix (Fin n) (Fin n) ℂ)
    (hE : Eᴴ * H * E = 1) : Function.Injective E.mulVec := by
  intro u v huv
  have h := congrArg (fun w => (Eᴴ * H) *ᵥ w) huv
  simpa only [Matrix.mulVec_mulVec, hE, Matrix.one_mulVec] using h

theorem relative_frame_diagonal (H G E : Matrix (Fin n) (Fin n) ℂ) (lam : Fin n → ℝ)
    (hE : Eᴴ * H * E = 1)
    (hG : G = H * E * Matrix.diagonal (fun i => (lam i : ℂ)) * Eᴴ * H) :
    Eᴴ * G * E = Matrix.diagonal (fun i => (lam i : ℂ)) := by
  calc
    _ = (Eᴴ * H * E) * Matrix.diagonal (fun i => (lam i : ℂ)) * (Eᴴ * H * E) := by
      rw [hG]
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [hE]; simp

theorem relative_frame_eigenvalues_pos (H G E : Matrix (Fin n) (Fin n) ℂ) (lam : Fin n → ℝ)
    (hGpos : G.PosDef) (hE : Eᴴ * H * E = 1)
    (hG : G = H * E * Matrix.diagonal (fun i => (lam i : ℂ)) * Eᴴ * H) :
    ∀ i, 0 < lam i := by
  have hdiag := hGpos.conjTranspose_mul_mul_same (relative_frame_mulVec_injective H E hE)
  rw [relative_frame_diagonal H G E lam hE hG] at hdiag
  have hpos := Matrix.posDef_diagonal_iff.mp hdiag
  intro i
  exact (Complex.pos_iff.mp (hpos i)).1

set_option maxHeartbeats 800000 in
theorem relative_frame_trace (H G E : Matrix (Fin n) (Fin n) ℂ) (lam : Fin n → ℝ)
    (hH : H.PosDef) (hE : Eᴴ * H * E = 1)
    (hG : G = H * E * Matrix.diagonal (fun i => (lam i : ℂ)) * Eᴴ * H) :
    (H⁻¹ * G).trace.re = ∑ i, lam i := by
  have hi := Yau.NodeProofs.P06Weitzenbock.inverseMetric_eq_unitary_frame H E hH hE
  have ht : (H⁻¹ * G).trace = (Matrix.diagonal (fun i => (lam i : ℂ))).trace := by
    rw [hi, hG]
    calc
      _ = (E * ((Eᴴ * H * E) * Matrix.diagonal (fun i => (lam i : ℂ)) * Eᴴ * H)).trace := by
        congr 1
        simp only [Matrix.mul_assoc]
      _ = (((Eᴴ * H * E) * Matrix.diagonal (fun i => (lam i : ℂ)) * Eᴴ * H) * E).trace :=
        Matrix.trace_mul_comm _ _
      _ = ((Eᴴ * H * E) * Matrix.diagonal (fun i => (lam i : ℂ)) * (Eᴴ * H * E)).trace := by
        congr 1
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [hE]; simp
  rw [ht, Matrix.trace_diagonal]
  exact Complex.re_sum _ _

theorem relative_frame_det_ratio (H G E : Matrix (Fin n) (Fin n) ℂ) (lam : Fin n → ℝ)
    (hH : H.PosDef) (hE : Eᴴ * H * E = 1)
    (hG : G = H * E * Matrix.diagonal (fun i => (lam i : ℂ)) * Eᴴ * H) :
    G.det.re / H.det.re = ∏ i, lam i := by
  have hEdet := congrArg Matrix.det hE
  simp only [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one] at hEdet
  have hdet : G.det = H.det * ∏ i, (lam i : ℂ) := by
    rw [hG]
    simp only [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_diagonal]
    calc
      _ = H.det * (star E.det * H.det * E.det) * ∏ i, (lam i : ℂ) := by ring
      _ = _ := by rw [hEdet]; ring
  have hre := congrArg Complex.re hdet
  rw [← Complex.ofReal_prod] at hre
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] at hre
  have hHpos : 0 < H.det.re := (Complex.pos_iff.mp hH.det_pos).1
  apply (div_eq_iff hHpos.ne').mpr
  simpa only [mul_comm] using hre

/-- Actual positive relative eigenvalues have exactly the metric trace and
Jacobian determinant quotient required by the singular-value argument. -/
theorem exists_relative_spectral_data (H G : Matrix (Fin n) (Fin n) ℂ)
    (hH : H.PosDef) (hG : G.PosDef) :
    ∃ (E : Matrix (Fin n) (Fin n) ℂ) (lam : Fin n → ℝ),
      Eᴴ * H * E = 1 ∧ Eᴴ * G * E = Matrix.diagonal (fun i => (lam i : ℂ)) ∧
      H⁻¹ = E * Eᴴ ∧ (∀ i, 0 < lam i) ∧
      (H⁻¹ * G).trace.re = ∑ i, lam i ∧ G.det.re / H.det.re = ∏ i, lam i := by
  obtain ⟨E, lam, hE, hdiag⟩ :=
    Yau.NodeProofs.P06Weitzenbock.exists_relative_unitary_eigenframe H G hH hG.isHermitian
  exact ⟨E, lam, hE, relative_frame_diagonal H G E lam hE hdiag,
    Yau.NodeProofs.P06Weitzenbock.inverseMetric_eq_unitary_frame H E hH hE,
    relative_frame_eigenvalues_pos H G E lam hG hE hdiag,
    relative_frame_trace H G E lam hH hE hdiag,
    relative_frame_det_ratio H G E lam hH hE hdiag⟩

end Yau.NodeProofs.D02Aux
