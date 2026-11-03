import Yau.Proofs.P06RelativePolynomial
import Yau.Proofs.P06FiberPolynomialAlgebra

noncomputable section
open scoped Matrix ComplexOrder MatrixOrder

namespace Yau.NodeProofs.P06Aux.Clip
variable {n : ℕ}

theorem aeval_similarity_two_sided (L R S : Matrix (Fin n) (Fin n) ℂ)
    (hRL : R * L = 1) (hLR : L * R = 1) (p : Polynomial ℝ) :
    Polynomial.aeval (L * S * R) p = L * Polynomial.aeval S p * R := by
  classical
  simp only [FiberPoly.aeval_sum, similarity_pow L R S hRL hLR,
    Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]

theorem aeval_real_diagonal (eig : Fin n → ℝ) (p : Polynomial ℝ) :
    Polynomial.aeval (Matrix.diagonal (fun i => (eig i : ℂ))) p =
      Matrix.diagonal (fun i => ((p.eval (eig i) : ℝ) : ℂ)) := by
  have hd := Polynomial.aeval_algHom_apply
    (Matrix.diagonalAlgHom ℝ : (Fin n → ℂ) →ₐ[ℝ] Matrix (Fin n) (Fin n) ℂ)
    (fun i => (eig i : ℂ)) p
  change Polynomial.aeval (Matrix.diagonal (fun i => (eig i : ℂ))) p =
    Matrix.diagonal (Polynomial.aeval (fun i => (eig i : ℂ)) p) at hd
  rw [hd]
  congr 1
  funext i
  rw [Polynomial.aeval_pi_apply₂]
  exact Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval (eig i) p

/-- Every relative unitary diagonalization is preserved by the actual
weighted polynomial, with the same frame and the evaluated eigenvalues. -/
theorem weightedPolynomial_spectral (H A E : Matrix (Fin n) (Fin n) ℂ)
    (hH : H.PosDef) (eig : Fin n → ℝ) (hE : Eᴴ * H * E = 1)
    (hA : A = H * E * Matrix.diagonal (fun i => (eig i : ℂ)) * Eᴴ * H)
    (p : Polynomial ℝ) :
    H * Polynomial.aeval (H⁻¹ * A) p =
      H * E * Matrix.diagonal (fun i => ((p.eval (eig i) : ℝ) : ℂ)) * Eᴴ * H := by
  let F := Eᴴ * H
  have hFE : F * E = 1 := hE
  have hEF : E * F = 1 := mul_eq_one_comm.mp hFE
  have hdiag : H⁻¹ * A = E * Matrix.diagonal (fun i => (eig i : ℂ)) * F := by
    rw [hA]
    dsimp only [F]
    rw [← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc,
      Matrix.nonsing_inv_mul H (hH.isUnit.map Matrix.detMonoidHom), one_mul]
    simp only [mul_assoc]
  rw [hdiag, aeval_similarity_two_sided E F _ hFE hEF, aeval_real_diagonal]
  simp only [F, mul_assoc]

theorem metricRoot_inv_mul_metric (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef) :
    (metricRoot H)⁻¹ * H = metricRoot H := by
  calc
    _ = (metricRoot H)⁻¹ * (metricRoot H * metricRoot H) :=
      congrArg (fun X : Matrix (Fin n) (Fin n) ℂ => (metricRoot H)⁻¹ * X) (metricRoot_sq H hH).symm
    _ = _ := by rw [← mul_assoc, metricRoot_inv_mul H hH, one_mul]

theorem metric_mul_metricRoot_inv (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef) :
    H * (metricRoot H)⁻¹ = metricRoot H := by
  calc
    _ = (metricRoot H * metricRoot H) * (metricRoot H)⁻¹ :=
      congrArg (fun X : Matrix (Fin n) (Fin n) ℂ => X * (metricRoot H)⁻¹) (metricRoot_sq H hH).symm
    _ = _ := by rw [mul_assoc, metricRoot_mul_inv H hH, mul_one]

theorem relativeUnitary_eigenvalue_bound (H A E : Matrix (Fin n) (Fin n) ℂ)
    (hH : H.PosDef) (eig : Fin n → ℝ) (hE : Eᴴ * H * E = 1)
    (hA : A = H * E * Matrix.diagonal (fun i => (eig i : ℂ)) * Eᴴ * H) (i : Fin n) :
    |eig i| ≤ ‖relativeMatrixHS H A‖ := by
  let Q := metricRoot H * E
  have hQ : Qᴴ * Q = 1 := by
    calc
      _ = Eᴴ * (metricRoot H * metricRoot H) * E := by
        simp only [Q, Matrix.conjTranspose_mul, (metricRoot_hermitian H).eq, mul_assoc]
      _ = 1 := by rw [metricRoot_sq H hH, hE]
  have hdiag : metricWhiten H A = Q * Matrix.diagonal (fun i => (eig i : ℂ)) * Qᴴ := by
    calc
      _ = ((metricRoot H)⁻¹ * H) * E * Matrix.diagonal (fun i => (eig i : ℂ)) *
          Eᴴ * (H * (metricRoot H)⁻¹) := by rw [metricWhiten, hA]; simp only [mul_assoc]
      _ = _ := by
        rw [metricRoot_inv_mul_metric H hH, metric_mul_metricRoot_inv H hH]
        simp only [Q, Matrix.conjTranspose_mul, (metricRoot_hermitian H).eq, mul_assoc]
  have he := matrixToHS_unitary_conjugation_sq Q (Matrix.diagonal (fun j => (eig j : ℂ))) hQ
  rw [← hdiag] at he
  have hn : ‖matrixToHS (Matrix.diagonal (fun j => (eig j : ℂ)))‖ = ‖relativeMatrixHS H A‖ := by
    change _ = ‖matrixToHS (metricWhiten H A)‖
    nlinarith [norm_nonneg (matrixToHS (metricWhiten H A)),
      norm_nonneg (matrixToHS (Matrix.diagonal (fun j => (eig j : ℂ))))]
  have hb := PiLp.norm_apply_le (matrixToHS (Matrix.diagonal (fun j => (eig j : ℂ)))) (i, i)
  change ‖(Matrix.diagonal (fun j => (eig j : ℂ)) i i)‖ ≤
    ‖matrixToHS (Matrix.diagonal (fun j => (eig j : ℂ)))‖ at hb
  rw [Matrix.diagonal_apply_eq, Complex.norm_real, Real.norm_eq_abs, hn] at hb
  exact hb

end Yau.NodeProofs.P06Aux.Clip
