import Yau.Proofs.D06NormEstimates

/-! Trace and Frobenius estimates in the symmetrized difference argument. -/

open scoped Matrix ComplexConjugate

noncomputable section
namespace Yau.NodeProofs.D06Aux

open Yau.Blueprint

variable {r : ℕ}

def entryVector (A : Matrix (Fin r) (Fin r) ℂ) : EuclideanSpace ℂ (Fin r × Fin r) :=
  WithLp.toLp 2 (fun ij => A ij.1 ij.2)

theorem norm_entryVector_sq (A : Matrix (Fin r) (Fin r) ℂ) :
    ‖entryVector A‖ ^ 2 = frobSq A := by
  simp only [EuclideanSpace.norm_sq_eq, entryVector,
    Fintype.sum_prod_type, frobSq]

theorem inner_entryVector (A B : Matrix (Fin r) (Fin r) ℂ) :
    inner ℂ (entryVector A) (entryVector B) = Matrix.trace (Aᴴ * B) := by
  simp only [entryVector, PiLp.inner_apply, RCLike.inner_apply',
    Fintype.sum_prod_type, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, RCLike.star_def]
  exact Finset.sum_comm

theorem frobSq_eq_re_trace (A : Matrix (Fin r) (Fin r) ℂ) :
    frobSq A = (Matrix.trace (Aᴴ * A)).re := by
  rw [← inner_entryVector, ← RCLike.re_to_complex, inner_self_eq_norm_sq,
    norm_entryVector_sq]

/-- Cauchy--Schwarz for the exact matrix Frobenius quantity. -/
theorem re_trace_mul_le (A B : Matrix (Fin r) (Fin r) ℂ) :
    (Matrix.trace (A * B)).re ≤ Real.sqrt (frobSq A) * Real.sqrt (frobSq B) := by
  have h := re_inner_le_norm (𝕜 := ℂ) (entryVector Aᴴ) (entryVector B)
  rw [inner_entryVector, Matrix.conjTranspose_conjTranspose] at h
  have hn (C : Matrix (Fin r) (Fin r) ℂ) : ‖entryVector C‖ = Real.sqrt (frobSq C) := by
    rw [← norm_entryVector_sq, Real.sqrt_sq (norm_nonneg _)]
  simpa only [hn, frobSq_conjTranspose, RCLike.re_to_complex] using h

/-- The source's pointwise trace estimate. This bound needs only the two
operator norm bounds; positivity is used when obtaining those bounds. -/
theorem re_trace_relative_difference_le (D X Y : Matrix (Fin r) (Fin r) ℂ) :
    (Matrix.trace (D * X * D * Y)).re ≤
      matOpNormR X * matOpNormR Y * frobSq D := by
  have hx : Real.sqrt (frobSq (D * X)) ≤ Real.sqrt (frobSq D) * matOpNormR X := by
    have h := Real.sqrt_le_sqrt (frobSq_mul_le_right D X)
    rwa [Real.sqrt_mul (frobSq_nonneg D), Real.sqrt_sq (matOpNormR_nonneg X)] at h
  have hy : Real.sqrt (frobSq (D * Y)) ≤ Real.sqrt (frobSq D) * matOpNormR Y := by
    have h := Real.sqrt_le_sqrt (frobSq_mul_le_right D Y)
    rwa [Real.sqrt_mul (frobSq_nonneg D), Real.sqrt_sq (matOpNormR_nonneg Y)] at h
  calc
    _ ≤ Real.sqrt (frobSq (D * X)) * Real.sqrt (frobSq (D * Y)) := by
      simpa only [Matrix.mul_assoc] using re_trace_mul_le (D * X) (D * Y)
    _ ≤ (Real.sqrt (frobSq D) * matOpNormR X) *
        (Real.sqrt (frobSq D) * matOpNormR Y) :=
      mul_le_mul hx hy (Real.sqrt_nonneg _)
        (mul_nonneg (Real.sqrt_nonneg _) (matOpNormR_nonneg X))
    _ = Real.sqrt (frobSq D) ^ 2 * (matOpNormR X * matOpNormR Y) := by ring
    _ = matOpNormR X * matOpNormR Y * frobSq D := by
      rw [Real.sq_sqrt (frobSq_nonneg D)]
      ring

theorem re_trace_symmetric_relative_difference_le
    (A B X Y : Matrix (Fin r) (Fin r) ℂ) (m : ℝ) (hm : 0 < m)
    (hAX : A * X = 1) (hXA : X * A = 1) (hBY : B * Y = 1)
    (hX : matOpNormR X ≤ m⁻¹) (hY : matOpNormR Y ≤ m⁻¹) :
    (Matrix.trace (B * X - 1)).re + (Matrix.trace (A * Y - 1)).re ≤
      (m ^ 2)⁻¹ * frobSq (B - A) := by
  have hnorm : matOpNormR X * matOpNormR Y ≤ (m ^ 2)⁻¹ := by
    calc
      _ ≤ m⁻¹ * m⁻¹ :=
        mul_le_mul hX hY (matOpNormR_nonneg Y) (inv_nonneg.mpr hm.le)
      _ = (m ^ 2)⁻¹ := by rw [← pow_two, inv_pow]
  calc
    _ = (Matrix.trace ((B - A) * X * (B - A) * Y)).re := by
      rw [symmetric_relative_difference A B X Y hAX hXA hBY, Matrix.trace_add,
        Complex.add_re]
    _ ≤ matOpNormR X * matOpNormR Y * frobSq (B - A) :=
      re_trace_relative_difference_le _ _ _
    _ ≤ (m ^ 2)⁻¹ * frobSq (B - A) :=
      mul_le_mul_of_nonneg_right hnorm (frobSq_nonneg _)

end Yau.NodeProofs.D06Aux
