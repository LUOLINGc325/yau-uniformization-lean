import Yau.Proofs.F01LargestRayleigh

/-! In the actual diagonal frame the largest Rayleigh value is attained by
the corresponding fixed coordinate direction. -/
noncomputable section
open scoped Matrix ComplexOrder
namespace Yau.NodeProofs.F01Aux
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem matrixQuadraticValue_single (H : Matrix ι ι ℂ) (i : ι) :
    matrixQuadraticValue H (Pi.single i 1) = (H i i).re := by
  simp [matrixQuadraticValue, Matrix.mulVec_single]

theorem matrixRayleigh_single (H K : Matrix ι ι ℂ) (i : ι) :
    matrixRayleigh H K (Pi.single i 1) = (K i i).re / (H i i).re := by
  rw [matrixRayleigh, matrixQuadraticValue_single, matrixQuadraticValue_single]

theorem real_diagonal_upper_order (values : ι → ℝ) {M : ℝ}
    (hM : ∀ i, values i ≤ M) :
    ((M : ℂ) • (1 : Matrix ι ι ℂ) - Matrix.diagonal (fun i => (values i : ℂ))).PosSemidef := by
  have heq : (M : ℂ) • (1 : Matrix ι ι ℂ) - Matrix.diagonal (fun i => (values i : ℂ)) =
      Matrix.diagonal (fun i => ((M - values i : ℝ) : ℂ)) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · simp [Matrix.one_apply, Matrix.diagonal_apply, hij]
  rw [heq]
  exact Matrix.PosSemidef.diagonal (fun i =>
    Complex.nonneg_iff.mpr ⟨sub_nonneg.mpr (hM i), by simp⟩)

theorem largestMatrixRayleigh_real_diagonal (values : ι → ℝ) (j : ι)
    (hvalues : ∀ i, values i ≤ values j) (hj : 0 ≤ values j) {c : ℝ} (hc : 0 < c) :
    largestMatrixRayleigh ((c : ℂ) • (1 : Matrix ι ι ℂ))
      (Matrix.diagonal (fun i => (values i : ℂ))) = values j / c := by
  have hH : ((c : ℂ) • (1 : Matrix ι ι ℂ)).PosDef :=
    Matrix.PosDef.one.smul (Complex.zero_lt_real.mpr hc)
  have horder : (((values j / c : ℝ) : ℂ) • ((c : ℂ) • (1 : Matrix ι ι ℂ)) -
      Matrix.diagonal (fun i => (values i : ℂ))).PosSemidef := by
    have hs : (((values j / c : ℝ) : ℂ) * (c : ℂ)) = (values j : ℂ) := by
      norm_cast
      exact div_mul_cancel₀ _ hc.ne'
    rw [smul_smul, hs]
    exact real_diagonal_upper_order values hvalues
  apply le_antisymm
  · exact largestMatrixRayleigh_le_of_order hH (div_nonneg hj hc.le) horder
  · apply le_csSup (⟨values j / c, by
      rintro _ ⟨v, rfl⟩
      exact matrixRayleigh_le_of_posSemidef hH (div_nonneg hj hc.le) horder v⟩)
    refine ⟨Pi.single j 1, ?_⟩
    rw [matrixRayleigh_single]
    simp

end Yau.NodeProofs.F01Aux
