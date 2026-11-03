import Yau.Proofs.P06RelativePolynomial
import Yau.Proofs.P06FiberPolynomialAlgebra
import Yau.Proofs.P06ClipBernstein
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity

noncomputable section
open Filter Set
open scoped Topology InnerProductSpace ComplexOrder MatrixOrder
namespace Yau.NodeProofs.P06Aux.FiberApprox
open Clip
variable {n : ℕ}

/-- The fixed finite spectral calculus is continuous in every eigenvalue sample. -/
theorem cfc_tendsto_of_eigenvalues (S : Matrix (Fin n) (Fin n) ℂ)
    (hS : S.IsHermitian) (F : ℕ → ℝ → ℝ) (f : ℝ → ℝ)
    (ht : ∀ i, Tendsto (fun j => F j (hS.eigenvalues i)) atTop
      (𝓝 (f (hS.eigenvalues i)))) :
    Tendsto (fun j => cfc (F j) S) atTop (𝓝 (cfc f S)) := by
  simp only [hS.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply,
    Unitary.coe_star, Matrix.star_eq_conjTranspose]
  have hd : Tendsto (fun j => Matrix.diagonal (fun i => (F j (hS.eigenvalues i) : ℂ)))
      atTop (𝓝 (Matrix.diagonal (fun i => (f (hS.eigenvalues i) : ℂ)))) := by
    have hc : Continuous (fun v : Fin n → ℂ => Matrix.diagonal v) := by fun_prop
    apply (hc.tendsto _).comp
    exact tendsto_pi_nhds.mpr (fun i => (Complex.continuous_ofReal.tendsto _).comp (ht i))
  exact (tendsto_const_nhds.mul hd).mul tendsto_const_nhds

/-- Polynomial spectral approximants converge at the actual fixed Hermitian matrix. -/
theorem aeval_tendsto_of_uniform (S : Matrix (Fin n) (Fin n) ℂ)
    (hS : S.IsHermitian) (p : ℕ → Polynomial ℝ) (f : ℝ → ℝ) {R : ℝ}
    (hs : ∀ i, hS.eigenvalues i ∈ Icc (-R) R)
    (ht : TendstoUniformlyOn (fun j x => (p j).eval x) f atTop (Icc (-R) R)) :
    Tendsto (fun j => Polynomial.aeval S (p j)) atTop (𝓝 (cfc f S)) := by
  have h := cfc_tendsto_of_eigenvalues S hS (fun j x => (p j).eval x) f
    (fun i => ht.tendsto_at (hs i))
  simpa only [cfc_polynomial _ S (show IsSelfAdjoint S from hS)] using h

/-- The finite Hilbert--Schmidt sum of a real functional calculus. -/
theorem matrixToHS_cfc_norm_sq (S : Matrix (Fin n) (Fin n) ℂ)
    (hS : S.IsHermitian) (f : ℝ → ℝ) :
    ‖matrixToHS (cfc f S)‖ ^ 2 = ∑ i, (f (hS.eigenvalues i)) ^ 2 := by
  let Q : Matrix (Fin n) (Fin n) ℂ := hS.eigenvectorUnitary
  have hQ : Q.conjTranspose * Q = 1 := by
    simpa only [Unitary.coe_star, Matrix.star_eq_conjTranspose] using
      Unitary.coe_star_mul_self hS.eigenvectorUnitary
  rw [hS.cfc_eq]
  change ‖matrixToHS (Q * Matrix.diagonal (fun i => (f (hS.eigenvalues i) : ℂ)) *
    Q.conjTranspose)‖ ^ 2 = _
  rw [matrixToHS_unitary_conjugation_sq Q _ hQ, matrixToHS_norm_sq]
  simp [Matrix.diagonal_apply, apply_ite, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- A zero-fixed polynomial with derivative bounded by one contracts the actual entry norm. -/
theorem aeval_matrixToHS_norm_le (S : Matrix (Fin n) (Fin n) ℂ)
    (hS : S.IsHermitian) (p : Polynomial ℝ) {R : ℝ}
    (hs : ∀ i, hS.eigenvalues i ∈ Icc (-R) R)
    (hR : 0 ≤ R) (h0 : p.eval 0 = 0)
    (hd : ∀ x ∈ Icc (-R) R, |p.derivative.eval x| ≤ 1) :
    ‖matrixToHS (Polynomial.aeval S p)‖ ≤ ‖matrixToHS S‖ := by
  have hp : ‖matrixToHS (Polynomial.aeval S p)‖ ^ 2 ≤ ‖matrixToHS S‖ ^ 2 := by
    rw [← cfc_polynomial p S (show IsSelfAdjoint S from hS), matrixToHS_cfc_norm_sq S hS]
    conv_rhs => rw [← cfc_id' ℝ S (show IsSelfAdjoint S from hS), matrixToHS_cfc_norm_sq S hS]
    apply Finset.sum_le_sum
    intro i hi
    have hb := polynomial_difference_sq_le p hd (hs i)
      (show (0 : ℝ) ∈ Icc (-R) R by constructor <;> linarith)
    simpa only [h0, sub_zero] using hb
  nlinarith [norm_nonneg (matrixToHS S), norm_nonneg (matrixToHS (Polynomial.aeval S p))]

/-- Every zero-fixed scalar contraction also contracts the genuine entry norm. -/
theorem cfc_matrixToHS_norm_le (S : Matrix (Fin n) (Fin n) ℂ)
    (hS : S.IsHermitian) (f : ℝ → ℝ) (hf : LipschitzWith 1 f) (h0 : f 0 = 0) :
    ‖matrixToHS (cfc f S)‖ ≤ ‖matrixToHS S‖ := by
  have hp : ‖matrixToHS (cfc f S)‖ ^ 2 ≤ ‖matrixToHS S‖ ^ 2 := by
    rw [matrixToHS_cfc_norm_sq S hS]
    conv_rhs => rw [← cfc_id' ℝ S (show IsSelfAdjoint S from hS), matrixToHS_cfc_norm_sq S hS]
    apply Finset.sum_le_sum
    intro i hi
    have hb := hf.dist_le_mul (hS.eigenvalues i) 0
    simp only [h0, Real.dist_eq, sub_zero, NNReal.coe_one, one_mul] at hb
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hb 2
  nlinarith [norm_nonneg (matrixToHS S), norm_nonneg (matrixToHS (cfc f S))]

/-- The same whitening identifies polynomial values, including the constant term. -/
theorem metricWhiten_aeval (H A : Matrix (Fin n) (Fin n) ℂ)
    (hH : H.PosDef) (p : Polynomial ℝ) :
    metricWhiten H (H * Polynomial.aeval (H⁻¹ * A) p) =
      Polynomial.aeval (metricWhiten H A) p := by
  rw [metricWhiten_metric_mul H _ hH]
  have he : Polynomial.aeval
      (metricRoot H * (H⁻¹ * A) * (metricRoot H)⁻¹) p =
      metricRoot H * Polynomial.aeval (H⁻¹ * A) p * (metricRoot H)⁻¹ := by
    simp only [FiberPoly.aeval_sum,
      similarity_pow (metricRoot H) (metricRoot H)⁻¹ (H⁻¹ * A)
        (metricRoot_inv_mul H hH) (metricRoot_mul_inv H hH),
      Finset.mul_sum, Finset.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
  rw [metricSimilarity_inverse_mul H A hH] at he
  exact he.symm

end Yau.NodeProofs.P06Aux.FiberApprox
