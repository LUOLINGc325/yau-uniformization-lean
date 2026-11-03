import Yau.Proofs.V04MajorantOrder
import Yau.Proofs.V03RectEntries
import Mathlib.Analysis.Matrix.PosDef

/-! Entry bounds for the actual spectral smoothing. Constants are uniform
for every positive delta at most one, and empty matrix indices are allowed. -/
open scoped Matrix Matrix.Norms.L2Operator ComplexOrder MatrixOrder
noncomputable section
namespace Yau.Blueprint.V04Proof.PositiveReplacementAux
open Yau Yau.Blueprint

variable {n : ℕ}

theorem posSemidef_rectOpNorm_le_trace (A : CotangentMatrix n) (hA : A.PosSemidef) :
    rectOpNorm A ≤ (Matrix.trace A).re := by
  have htr : (Matrix.trace A).re = ∑ i, hA.1.eigenvalues i := by
    simpa only [Complex.re_sum, RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_re] using
      congrArg Complex.re hA.1.trace_eq_sum_eigenvalues
  have hnon : 0 ≤ (Matrix.trace A).re := (Complex.nonneg_iff.mp hA.trace_nonneg).1
  change ‖A‖ ≤ _
  calc
    ‖A‖ = ‖cfc (fun x : ℝ => x) A‖ := congrArg norm
      (cfc_id' (R := ℝ) A (show IsSelfAdjoint A from hA.1)).symm
    _ ≤ (Matrix.trace A).re := ?_
  apply norm_cfc_le hnon
  intro x hx
  obtain ⟨i, rfl⟩ := hA.1.spectrum_real_eq_range_eigenvalues ▸ hx
  rw [Real.norm_eq_abs, abs_of_nonneg (hA.eigenvalues_nonneg i), htr]
  exact Finset.single_le_sum (fun j _ => hA.eigenvalues_nonneg j) (Finset.mem_univ i)

theorem smoothMajorant_rectOpNorm_bound {δ M : ℝ} (hδ : 0 < δ) (hM : 0 ≤ M)
    (A : CotangentMatrix n) (hA : A.IsHermitian) (hbound : rectOpNorm A ≤ M) :
    rectOpNorm (smoothMajorant δ A) ≤ M + 2 * δ := by
  change ‖smoothMajorant δ A‖ ≤ _
  rw [smoothMajorant_eq_cfc δ A hA]
  apply norm_cfc_le (by positivity)
  intro x hx
  have hxnorm := IsometricContinuousFunctionalCalculus.norm_spectrum_le A hx
    (show IsSelfAdjoint A from hA)
  have hxabsA : |x| ≤ ‖A‖ := by simpa only [Real.norm_eq_abs] using hxnorm
  have hxabs : |x| ≤ M := hxabsA.trans hbound
  have hb := scalarMajorant_bounds hδ x
  rw [Real.norm_eq_abs, abs_of_nonneg (hδ.le.trans hb.1)]
  have hmax : max x 0 ≤ M := max_le ((le_abs_self x).trans hxabs) hM
  linarith only [hb.2.2.2, hmax, hδ]

theorem smoothMajorant_sub_positive_rectOpNorm {δ : ℝ} (hδ : 0 < δ)
    (A : CotangentMatrix n) (hA : A.IsHermitian) :
    rectOpNorm (smoothMajorant δ A - matrixPositive A) ≤ 3 * δ / 2 := by
  change ‖smoothMajorant δ A - matrixPositive A‖ ≤ _
  rw [smoothMajorant_eq_cfc δ A hA, matrixPositive, hermitianScalar_eq_cfc _ A hA,
    ← cfc_sub (scalarMajorant δ) (fun x : ℝ => max x 0) A
      (scalarMajorant_contDiff hδ).continuous.continuousOn
      (continuous_id.max continuous_const).continuousOn]
  apply norm_cfc_le (by positivity)
  intro x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (scalarMajorant_bounds hδ x).2.2.1]
  exact (scalarMajorant_bounds hδ x).2.2.2

theorem symbol_smoothing_entry_error {δ : ℝ} (hδ : 0 < δ)
    (A : CotangentMatrix n) (hA : A.IsHermitian) (i j : CotangentIndex n) :
    ‖A i j - smoothMajorant δ A i j‖ ≤
      (Matrix.trace (matrixNegative A)).re + 3 * δ / 2 := by
  have he : A - smoothMajorant δ A =
      -matrixNegative A - (smoothMajorant δ A - matrixPositive A) := by
    calc
      A - smoothMajorant δ A = (matrixPositive A - matrixNegative A) - smoothMajorant δ A :=
        congrArg (fun B => B - smoothMajorant δ A) (matrixPositive_sub_matrixNegative A hA).symm
      _ = _ := by abel
  change ‖(A - smoothMajorant δ A) i j‖ ≤ _
  rw [he, Matrix.sub_apply, Matrix.neg_apply]
  calc
    _ ≤ ‖matrixNegative A i j‖ + ‖(smoothMajorant δ A - matrixPositive A) i j‖ := by
      simpa only [norm_neg] using norm_sub_le (-matrixNegative A i j)
        ((smoothMajorant δ A - matrixPositive A) i j)
    _ ≤ _ := add_le_add
      ((V03Proof.matrix_entry_norm_le_rectOpNorm _ i j).trans
        (posSemidef_rectOpNorm_le_trace _ (matrixNegative_posSemidef A)))
      ((V03Proof.matrix_entry_norm_le_rectOpNorm _ i j).trans
        (smoothMajorant_sub_positive_rectOpNorm hδ A hA))

end Yau.Blueprint.V04Proof.PositiveReplacementAux
