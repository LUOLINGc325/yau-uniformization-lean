import Yau.Proofs.P06SpectralClipComplex

noncomputable section
open scoped InnerProductSpace

namespace Yau.NodeProofs.P06Aux.Clip
variable {n : ℕ}

theorem matrixToHS_inner_trace (A B : Matrix (Fin n) (Fin n) ℂ) :
    inner ℝ (matrixToHS A) (matrixToHS B) = (Matrix.trace (A.conjTranspose * B)).re := by
  rw [PiLp.inner_apply]
  simp only [matrixToHS, PiLp.toLp_apply, real_inner_eq_re_inner ℂ, RCLike.re_eq_complex_re]
  rw [← Complex.re_sum]
  apply congrArg Complex.re
  simp only [RCLike.inner_apply', Fintype.sum_prod_type,
    Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  simp only [← Complex.star_def]
  exact Finset.sum_comm

theorem matrixToHS_norm_sq_trace (D : Matrix (Fin n) (Fin n) ℂ) :
    ‖matrixToHS D‖ ^ 2 = (Matrix.trace (D.conjTranspose * D)).re := by
  simpa only [real_inner_self_eq_norm_sq] using matrixToHS_inner_trace D D

theorem unitary_conjugation_mul (Q A B : Matrix (Fin n) (Fin n) ℂ)
    (hQ : Q.conjTranspose * Q = 1) :
    (Q * A * Q.conjTranspose) * (Q * B * Q.conjTranspose) = Q * (A * B) * Q.conjTranspose := by
  calc
    _ = Q * A * (Q.conjTranspose * Q) * B * Q.conjTranspose := by simp only [mul_assoc]
    _ = _ := by rw [hQ]; simp only [mul_one, mul_assoc]

theorem matrixToHS_unitary_conjugation_sq (Q D : Matrix (Fin n) (Fin n) ℂ)
    (hQ : Q.conjTranspose * Q = 1) :
    ‖matrixToHS (Q * D * Q.conjTranspose)‖ ^ 2 = ‖matrixToHS D‖ ^ 2 := by
  rw [matrixToHS_norm_sq_trace, matrixToHS_norm_sq_trace]
  have ht : (Q * D * Q.conjTranspose).conjTranspose = Q * D.conjTranspose * Q.conjTranspose := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, mul_assoc]
  rw [ht, unitary_conjugation_mul Q _ _ hQ, Matrix.trace_mul_cycle, ← mul_assoc, hQ, one_mul]

theorem polynomialVariation_unitary_conjugation
    (Q : Matrix.unitaryGroup (Fin n) ℂ) (S D : Matrix (Fin n) (Fin n) ℂ) (p : Polynomial ℝ) :
    polynomialVariation p ((Q : Matrix (Fin n) (Fin n) ℂ) * S * (Q : Matrix (Fin n) (Fin n) ℂ).conjTranspose)
      ((Q : Matrix (Fin n) (Fin n) ℂ) * D * (Q : Matrix (Fin n) (Fin n) ℂ).conjTranspose) =
      (Q : Matrix (Fin n) (Fin n) ℂ) * polynomialVariation p S D *
        (Q : Matrix (Fin n) (Fin n) ℂ).conjTranspose := by
  simpa only [AlgEquiv.coe_toAlgHom, StarAlgEquiv.coe_toAlgEquiv,
    Unitary.conjStarAlgAut_apply, Unitary.coe_star, Matrix.star_eq_conjTranspose] using
    polynomialVariation_map (Unitary.conjStarAlgAut ℝ (Matrix (Fin n) (Fin n) ℂ) Q).toAlgEquiv.toAlgHom p S D

/-- The full polynomial differential contracts the genuine complex entry
Hilbert norm at any Hermitian matrix and any matrix direction. -/
theorem polynomialVariation_hermitian_energy_le
    (p : Polynomial ℝ) (S D : Matrix (Fin n) (Fin n) ℂ) (hS : S.IsHermitian) {R : ℝ}
    (hlam : ∀ i, hS.eigenvalues i ∈ Set.Icc (-R) R)
    (hder : ∀ x ∈ Set.Icc (-R) R, |p.derivative.eval x| ≤ 1) :
    ‖matrixToHS (polynomialVariation p S D)‖ ^ 2 ≤ ‖matrixToHS D‖ ^ 2 := by
  classical
  let Q : Matrix (Fin n) (Fin n) ℂ := hS.eigenvectorUnitary
  have hQ : Q.conjTranspose * Q = 1 := by
    simpa only [Unitary.coe_star, Matrix.star_eq_conjTranspose] using
      Unitary.coe_star_mul_self hS.eigenvectorUnitary
  have hQt : Q * Q.conjTranspose = 1 := by
    simpa only [Unitary.coe_star, Matrix.star_eq_conjTranspose] using
      Unitary.coe_mul_star_self hS.eigenvectorUnitary
  have hdiag : S = Q * Matrix.diagonal (fun i => (hS.eigenvalues i : ℂ)) * Q.conjTranspose := by
    simpa only [Unitary.conjStarAlgAut_apply, Unitary.coe_star, Matrix.star_eq_conjTranspose,
      RCLike.ofReal_eq_complex_ofReal, Function.comp_def] using hS.spectral_theorem
  let D' := Q.conjTranspose * D * Q
  have hD : Q * D' * Q.conjTranspose = D := by
    calc
      _ = (Q * Q.conjTranspose) * D * (Q * Q.conjTranspose) := by
        dsimp only [D']; simp only [mul_assoc]
      _ = D := by rw [hQt]; simp only [one_mul, mul_one]
  have hvar := polynomialVariation_unitary_conjugation hS.eigenvectorUnitary
    (Matrix.diagonal (fun i => (hS.eigenvalues i : ℂ))) D' p
  change polynomialVariation p (Q * _ * Q.conjTranspose) (Q * D' * Q.conjTranspose) = _ at hvar
  rw [← hdiag, hD] at hvar
  calc
    _ = ‖matrixToHS (polynomialVariation p (Matrix.diagonal (fun i => (hS.eigenvalues i : ℂ))) D')‖ ^ 2 := by
      rw [hvar, matrixToHS_unitary_conjugation_sq Q _ hQ]
    _ ≤ ‖matrixToHS D'‖ ^ 2 := polynomialVariation_complex_diagonal_energy_le p _ _ hlam hder
    _ = ‖matrixToHS D‖ ^ 2 := by
      have he := matrixToHS_unitary_conjugation_sq Q D' hQ
      rw [hD] at he
      exact he.symm

theorem abs_eigenvalues_le_matrixToHS (S : Matrix (Fin n) (Fin n) ℂ)
    (hS : S.IsHermitian) (i : Fin n) : |hS.eigenvalues i| ≤ ‖matrixToHS S‖ := by
  let Q : Matrix (Fin n) (Fin n) ℂ := hS.eigenvectorUnitary
  have hQ : Q.conjTranspose * Q = 1 := by
    simpa only [Unitary.coe_star, Matrix.star_eq_conjTranspose] using
      Unitary.coe_star_mul_self hS.eigenvectorUnitary
  have hdiag : S = Q * Matrix.diagonal (fun j => (hS.eigenvalues j : ℂ)) * Q.conjTranspose := by
    simpa only [Unitary.conjStarAlgAut_apply, Unitary.coe_star, Matrix.star_eq_conjTranspose,
      RCLike.ofReal_eq_complex_ofReal, Function.comp_def] using hS.spectral_theorem
  have heq : ‖matrixToHS (Matrix.diagonal (fun j => (hS.eigenvalues j : ℂ)))‖ = ‖matrixToHS S‖ := by
    have he := matrixToHS_unitary_conjugation_sq Q
      (Matrix.diagonal (fun j => (hS.eigenvalues j : ℂ))) hQ
    rw [← hdiag] at he
    nlinarith [norm_nonneg (matrixToHS S),
      norm_nonneg (matrixToHS (Matrix.diagonal (fun j => (hS.eigenvalues j : ℂ))))]
  have hb := PiLp.norm_apply_le (matrixToHS (Matrix.diagonal (fun j => (hS.eigenvalues j : ℂ)))) (i, i)
  change ‖(Matrix.diagonal (fun j => (hS.eigenvalues j : ℂ)) i i)‖ ≤
    ‖matrixToHS (Matrix.diagonal (fun j => (hS.eigenvalues j : ℂ)))‖ at hb
  rw [Matrix.diagonal_apply_eq, Complex.norm_real, Real.norm_eq_abs, heq] at hb
  exact hb

end Yau.NodeProofs.P06Aux.Clip
