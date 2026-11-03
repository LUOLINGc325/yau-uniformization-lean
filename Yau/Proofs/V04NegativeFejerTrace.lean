import Yau.Proofs.V04FejerHermitian
import Yau.Proofs.V04TraceSquareError
import Yau.Proofs.V04AverageSquares

/-! The actual frozen Fejer columns test the negative cubic trace. The
comparison error is the square root of the original Frobenius average,
with a uniform symbol-dependent coefficient and no interchange of limits. -/

open MeasureTheory
open scoped Matrix Topology ComplexOrder ContDiff
noncomputable section
namespace Yau.Blueprint.V04Proof
open Yau Yau.Blueprint Yau.Blueprint.V03Proof

variable {n q : ℕ} {X : KahlerManifold n}

theorem negativeTrace_cube_le_fejer_tests {d : VariationData X q} (hd : VariationSetup d)
    {j a : ℕ} (ha : 4 ≤ a) {F : VariationDisc X} (hF : AdmissibleVariationDisc d j F)
    {E : ℂ → CotangentMatrix n} (hE : NormalizedDiscFrame d.G F.f E) {M : ℝ} (hM : 0 ≤ M)
    (hT : ∀ θ, (boundarySymbol d j a F E (circlePoint θ)).IsHermitian ∧
      rectOpNorm (boundarySymbol d j a F E (circlePoint θ)) ≤ M) (P : ℕ) :
    negativeTrace d j a F E 3 ≤
      -(∑ i, circleAverage (fun θ => quadValue (boundarySymbol d j a F E (circlePoint θ))
        (fejerTestColumn d j a F E P i (circlePoint θ)))) +
      (2 * (((2 * n : ℕ) : ℝ) * M) ^ 2) * Real.sqrt (negativeFejerError d j a F E P) := by
  let T := fun θ => boundarySymbol d j a F E (circlePoint θ)
  let N := fun θ => matrixNegative (T θ)
  let S := fun θ => fejerMean N P θ
  let f := fun θ => ‖cotangentMatrixHS (S θ - N θ)‖
  let g := fun θ => (Matrix.trace (T θ * S θ ^ 2)).re
  let c := fun θ => (Matrix.trace (N θ ^ 3)).re
  let Q : ℝ := 2 * (((2 * n : ℕ) : ℝ) * M) ^ 2
  have hQ : 0 ≤ Q := by positivity
  have hTc : ∀ i k, Continuous (fun θ => T θ i k) :=
    fun i k => (boundarySymbol_trace_contDiff hd j a ha F hF E hE i k).continuous
  have hNc : ∀ i k, Continuous (fun θ => N θ i k) :=
    matrixNegative_entry_continuous hTc (fun θ => (hT θ).1)
  have hSc : ∀ i k, Continuous (fun θ => S θ i k) := fejerMean_entry_continuous N P
  have hNp : ∀ i k, Function.Periodic (fun θ => N θ i k) (2 * Real.pi) :=
    fun i k => circleTrace_periodic (fun z => matrixNegative (boundarySymbol d j a F E z) i k)
  have hSH (θ : ℝ) : (S θ).IsHermitian :=
    fejerMean_isHermitian N hNc hNp (fun t => (matrixNegative_posSemidef (T t)).1) P θ
  have hTe (θ : ℝ) (i k : CotangentIndex n) : ‖T θ i k‖ ≤ M :=
    (matrix_entry_norm_le_rectOpNorm _ i k).trans (hT θ).2
  have hNe (θ : ℝ) (i k : CotangentIndex n) : ‖N θ i k‖ ≤ M :=
    (matrix_entry_norm_le_rectOpNorm _ i k).trans
      ((rectOpNorm_negative_le _ (hT θ).1).trans (hT θ).2)
  have hSe (θ : ℝ) (i k : CotangentIndex n) : ‖S θ i k‖ ≤ M :=
    fejerMean_entry_norm_le N hNc hNp hNe P θ i k
  have hf : Continuous f := by
    apply Continuous.norm
    exact (PiLp.continuous_toLp 2 _).comp
      (continuous_pi (fun p => (hSc p.1 p.2).sub (hNc p.1 p.2)))
  have hg : Continuous g := by
    have hTm : Continuous T := continuous_pi (fun i => continuous_pi (hTc i))
    have hSm : Continuous S := continuous_pi (fun i => continuous_pi (hSc i))
    have hprod : Continuous (fun θ => T θ * S θ ^ 2) := by
      simpa only [pow_two] using hTm.matrix_mul (hSm.matrix_mul hSm)
    exact Complex.continuous_re.comp hprod.matrix_trace
  have hc : Continuous c := matrixNegative_trace_pow_continuous hTc (fun θ => (hT θ).1) 3
  have hpoint (θ : ℝ) : g θ + c θ ≤ Q * f θ := by
    have hh := trace_square_difference_le (T θ) (S θ) (N θ) (hT θ).1
      (mul_nonneg (by positivity) hM)
      (matrixHS_norm_le_of_entries _ hM (hTe θ))
      (matrixHS_norm_le_of_entries _ hM (hSe θ))
      (matrixHS_norm_le_of_entries _ hM (hNe θ))
    have heq : (Matrix.trace (T θ * (S θ ^ 2 - N θ ^ 2))).re = g θ + c θ := by
      rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
      change (Matrix.trace (T θ * S θ ^ 2)).re -
        (Matrix.trace (T θ * matrixNegative (T θ) ^ 2)).re = _
      rw [trace_mul_negative_sq _ (hT θ).1]
      change g θ - -c θ = g θ + c θ
      ring
    rw [heq] at hh
    exact (le_abs_self _).trans hh
  have havg : circleAverage g + circleAverage c ≤ Q * circleAverage f := by
    have hl : circleAverage (fun θ => g θ + c θ) ≤ circleAverage (fun θ => Q * f θ) :=
      circleAverage_mono_of_continuous (hg.add hc) (continuous_const.mul hf) hpoint
    rwa [circleAverage_add_of_continuous hg hc, circleAverage_const_mul] at hl
  have hsqrt : circleAverage f ≤ Real.sqrt (negativeFejerError d j a F E P) := by
    have hh := circleAverage_le_sqrt_square f hf (fun _ => norm_nonneg _)
    have heq : circleAverage (fun θ => f θ ^ 2) = negativeFejerError d j a F E P := by
      apply congrArg circleAverage
      funext θ
      exact cotangentMatrixHS_norm_sq (S θ - N θ)
    rwa [heq] at hh
  have hquad (θ : ℝ) : (∑ i, quadValue (T θ)
      (fejerTestColumn d j a F E P i (circlePoint θ))) = g θ := by
    calc
      _ = ∑ i, quadValue (T θ) (fun r => S θ r i) := by
        apply Finset.sum_congr rfl
        intro i _
        have heq : fejerTestColumn d j a F E P i (circlePoint θ) =
            (circlePoint θ ^ (P + 1)) • (fun r => S θ r i) := by
          funext r
          exact fejerTestColumn_boundary d j a F E P i r θ
        rw [heq, quadValue_smul, norm_pow]
        have hcircle : ‖circlePoint θ‖ = 1 := by simp [circlePoint, Complex.norm_exp]
        rw [hcircle, one_pow, one_pow, one_mul]
      _ = _ := sum_quadValue_columns_hermitian _ _ (hSH θ)
  have hsum : (∑ i, circleAverage (fun θ => quadValue (T θ)
      (fejerTestColumn d j a F E P i (circlePoint θ)))) = circleAverage g := by
    have hh := circleAverage_finsetSum Finset.univ
      (fun i θ => quadValue (T θ) (fejerTestColumn d j a F E P i (circlePoint θ)))
      (fun i _ => quadValue_continuous hTc (fun r =>
        (closedDisc_scalar_trace_contDiff (fejerTestColumn_holomorphic d j a F E P i r)).continuous))
    rw [show (fun θ => ∑ i, quadValue (T θ)
        (fejerTestColumn d j a F E P i (circlePoint θ))) = g from funext hquad] at hh
    exact hh.symm
  rw [hsum]
  change circleAverage c ≤ -circleAverage g + Q * Real.sqrt (negativeFejerError d j a F E P)
  have hh := mul_le_mul_of_nonneg_left hsqrt hQ
  linarith only [havg, hh]

end Yau.Blueprint.V04Proof
