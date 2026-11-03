import Yau.LeafProofs.L03DiracCutoffSymbols

open MeasureTheory Filter
open scoped Topology ContDiff

noncomputable section

namespace Yau.LeafProofs.L03

variable {n k : ℕ} {M : ComplexManifold n}

theorem realForm_eq_of_center_chart_eq (A B : RealForm M k)
    (h : ∀ x, chartForm A x (chartPt x x) = chartForm B x (chartPt x x)) : A = B := by
  funext x
  apply sub_eq_zero.mp
  apply (formComponents_center_eq_zero_iff (A - B) x).mp
  funext I
  change formComponents A x (chartPt x x) I - formComponents B x (chartPt x x) I = 0
  exact sub_eq_zero.mpr (congrArg (fun P => P (fun r => realVec (I r))) (h x))

theorem chartForm_multiply (η : M.Carrier → ℝ) (A : RealForm M k)
    (x : M.Carrier) (z : ComplexVector n) :
    chartForm (multiplyRealForm η A) x z = η (chartInv x z) • chartForm A x z := by
  ext v
  rfl

theorem modelExteriorSymbol_smul_covector (ξ : ComplexVector n →L[ℝ] ℝ)
    (P : (ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ) (c : ℝ) :
    modelExteriorSymbol (c • ξ) P = c • modelExteriorSymbol ξ P := by
  ext v
  simp only [modelExteriorSymbol_apply, smul_apply,
    ContinuousAlternatingMap.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem modelMetricSharp_smul_covector (B : Matrix (RIdx n) (RIdx n) ℝ)
    (ξ : ComplexVector n →L[ℝ] ℝ) (c : ℝ) :
    modelMetricSharp B (c • ξ) = c • modelMetricSharp B ξ := by
  simp only [modelMetricSharp, smul_apply, smul_eq_mul, Finset.smul_sum, smul_smul]
  congr 1
  funext i
  congr 1
  funext j
  congr 1
  ring

theorem fderiv_inChart_square (η : M.Carrier → ℝ) (hη : SmoothFn η)
    (x : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget x) :
    fderiv ℝ (inChart x (fun y => η y * η y)) z =
      (2 * η (chartInv x z)) • fderiv ℝ (inChart x η) z := by
  have hd := ((hη x).contDiffAt
    ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).differentiableAt (by simp)
  change fderiv ℝ (fun w => inChart x η w * inChart x η w) z = _
  rw [fderiv_fun_mul hd hd]
  ext v
  simp only [add_apply, smul_apply, smul_eq_mul]
  change η (chartInv x z) * _ + η (chartInv x z) * _ = (2 * η (chartInv x z)) * _
  ring

/-- Squaring the scalar cutoff doubles its actual first-order exterior
commutator, with the original fixed exterior operator. -/
theorem exteriorCutoffError_square (η : M.Carrier → ℝ) (hη : SmoothFn η)
    (A : RealForm M k) (hA : SmoothRealForm A) :
    exteriorCutoffError (fun y => η y * η y) A =
      multiplyRealForm (fun y => 2 * η y) (exteriorCutoffError η A) := by
  apply realForm_eq_of_center_chart_eq
  intro x
  have hz : chartPt x x ∈ chartTarget x := mem_extChartAt_target x
  rw [exteriorCutoffError_to_chart (fun y => η y * η y) (fun y => (hη y).mul (hη y)) A hA x hz,
    chartForm_multiply, exteriorCutoffError_to_chart η hη A hA x hz,
    fderiv_inChart_square η hη x hz, modelExteriorSymbol_smul_covector]

/-- The same exact scalar-square product rule for the actual
codifferential, including its negative contraction sign. -/
theorem codifferentialCutoffError_square (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (η : M.Carrier → ℝ) (hη : SmoothFn η)
    (A : RealForm M (k + 1)) (hA : SmoothRealForm A) :
    codifferentialCutoffError g.form (fun y => η y * η y) A =
      multiplyRealForm (fun y => 2 * η y) (codifferentialCutoffError g.form η A) := by
  apply realForm_eq_of_center_chart_eq
  intro x
  have hz : chartPt x x ∈ chartTarget x := mem_extChartAt_target x
  rw [codifferentialCutoffError_to_chart g μ hμ (fun y => η y * η y) (fun y => (hη y).mul (hη y)) A hA x hz,
    chartForm_multiply, codifferentialCutoffError_to_chart g μ hμ η hη A hA x hz,
    fderiv_inChart_square η hη x hz, modelMetricSharp_smul_covector, map_smul, smul_neg]

/-- The combined exterior/contraction error has exactly the scalar
gradient energy, with the genuine normalized form metric. -/
theorem cutoffErrors_normSq (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (η : M.Carrier → ℝ) (hη : SmoothFn η)
    (A : RealForm M (k + 1)) (hA : SmoothRealForm A) (y : M.Carrier) :
    formNormSq g.form (exteriorCutoffError η A) y +
        formNormSq g.form (codifferentialCutoffError g.form η A) y =
      L18Aux.scalarGradientPair g.form η η y * formNormSq g.form A y := by
  let z := chartPt y y
  have hz : z ∈ chartTarget y := mem_extChartAt_target y
  have hi : chartInv y z = y := (extChartAt (ComplexModel n) y).left_inv (mem_extChartAt_source y)
  have he := modelFormInner_chartForm g.form (exteriorCutoffError η A) (exteriorCutoffError η A) y hz
  have hd := modelFormInner_chartForm g.form (codifferentialCutoffError g.form η A)
    (codifferentialCutoffError g.form η A) y hz
  simp only [exteriorCutoffError_to_chart η hη A hA y hz, hi] at he
  simp only [codifferentialCutoffError_to_chart g μ hμ η hη A hA y hz,
    modelFormInner_neg_self, hi] at hd
  change _ = formNormSq g.form (exteriorCutoffError η A) y at he
  change _ = formNormSq g.form (codifferentialCutoffError g.form η A) y at hd
  rw [← he, ← hd]
  have h := actual_symbol_energy g.form A hη y hz
  dsimp only at h
  rw [hi] at h
  exact h

theorem exteriorCutoffError_zero_normSq (g : HermitianField M)
    (η : M.Carrier → ℝ) (hη : SmoothFn η)
    (A : RealForm M 0) (hA : SmoothRealForm A) (y : M.Carrier) :
    formNormSq g (exteriorCutoffError η A) y =
      L18Aux.scalarGradientPair g η η y * formNormSq g A y := by
  let z := chartPt y y
  have hz : z ∈ chartTarget y := mem_extChartAt_target y
  have hi : chartInv y z = y := (extChartAt (ComplexModel n) y).left_inv (mem_extChartAt_source y)
  have he := modelFormInner_chartForm g (exteriorCutoffError η A) (exteriorCutoffError η A) y hz
  simp only [exteriorCutoffError_to_chart η hη A hA y hz, hi] at he
  change _ = formNormSq g (exteriorCutoffError η A) y at he
  rw [← he]
  have h := actual_symbol_energy_zero g A hη y hz
  dsimp only at h
  rw [hi] at h
  exact h

theorem exteriorCutoff_decomposition (η : M.Carrier → ℝ) (A : RealForm M k) :
    exteriorRealForm (multiplyRealForm η A) =
      multiplyRealForm η (exteriorRealForm A) + exteriorCutoffError η A := by
  unfold exteriorCutoffError
  abel

theorem codifferentialCutoff_decomposition (g : HermitianField M)
    (η : M.Carrier → ℝ) (A : RealForm M (k + 1)) :
    codifferentialRealForm g (multiplyRealForm η A) =
      multiplyRealForm η (codifferentialRealForm g A) + codifferentialCutoffError g η A := by
  unfold codifferentialCutoffError
  abel

theorem formNormSq_cutoff_algebra (g : HermitianField M) (η : M.Carrier → ℝ)
    (X E : RealForm M k) (y : M.Carrier) :
    formNormSq g (multiplyRealForm η X + E) y =
      formInner g X (multiplyRealForm (fun t => η t * η t) X +
        multiplyRealForm (fun t => 2 * η t) E) y + formNormSq g E y := by
  rw [formNormSq_add_eq, multiplyRealForm_normSq, formInner_add_right]
  simp only [Pi.add_apply, multiplyRealForm_inner_left, multiplyRealForm_inner_right]
  change _ = η y * η y * formNormSq g X y + _ + _
  ring

theorem exterior_cutoff_energy (g : HermitianField M)
    (η : M.Carrier → ℝ) (hη : SmoothFn η)
    (A : RealForm M k) (hA : SmoothRealForm A) (y : M.Carrier) :
    formNormSq g (exteriorRealForm (multiplyRealForm η A)) y =
      formInner g (exteriorRealForm A) (exteriorRealForm (multiplyRealForm (fun t => η t * η t) A)) y +
        formNormSq g (exteriorCutoffError η A) y := by
  rw [exteriorCutoff_decomposition η A, exteriorCutoff_decomposition (fun t => η t * η t) A,
    exteriorCutoffError_square η hη A hA]
  exact formNormSq_cutoff_algebra g η _ _ y

theorem codifferential_cutoff_energy (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (η : M.Carrier → ℝ) (hη : SmoothFn η)
    (A : RealForm M (k + 1)) (hA : SmoothRealForm A) (y : M.Carrier) :
    formNormSq g.form (codifferentialRealForm g.form (multiplyRealForm η A)) y =
      formInner g.form (codifferentialRealForm g.form A)
        (codifferentialRealForm g.form (multiplyRealForm (fun t => η t * η t) A)) y +
        formNormSq g.form (codifferentialCutoffError g.form η A) y := by
  rw [codifferentialCutoff_decomposition g.form η A,
    codifferentialCutoff_decomposition g.form (fun t => η t * η t) A,
    codifferentialCutoffError_square g μ hμ η hη A hA]
  exact formNormSq_cutoff_algebra g.form η _ _ y

/-- The actual first-order quadratic form of the original Hodge expression,
with its genuine degree-zero convention. -/
def hodgeEnergyDensity (g : HermitianField M) :
    (j : ℕ) → RealForm M j → RealForm M j → M.Carrier → ℝ
  | 0, A, B => formInner g (exteriorRealForm A) (exteriorRealForm B)
  | j + 1, A, B => formInner g (codifferentialRealForm g A) (codifferentialRealForm g B) +
      formInner g (exteriorRealForm A) (exteriorRealForm B)

theorem hodgeEnergyDensity_self_nonneg (g : HermitianField M)
    (A : RealForm M k) (y : M.Carrier) : 0 ≤ hodgeEnergyDensity g k A A y := by
  cases k with
  | zero => exact formNormSq_nonneg g _ y
  | succ j => exact add_nonneg (formNormSq_nonneg g _ y) (formNormSq_nonneg g _ y)

/-- Exact physical real Hodge IMS identity for the fixed actual d and δ.
Only the first derivative of the scalar cutoff remains. -/
theorem hodgeEnergyDensity_cutoff (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (η : M.Carrier → ℝ) (hη : SmoothFn η)
    (A : RealForm M k) (hA : SmoothRealForm A) (y : M.Carrier) :
    hodgeEnergyDensity g.form k (multiplyRealForm η A) (multiplyRealForm η A) y =
      hodgeEnergyDensity g.form k A (multiplyRealForm (fun t => η t * η t) A) y +
        L18Aux.scalarGradientPair g.form η η y * formNormSq g.form A y := by
  cases k with
  | zero =>
      exact (exterior_cutoff_energy g.form η hη A hA y).trans
        (congrArg (_ + ·) (exteriorCutoffError_zero_normSq g.form η hη A hA y))
  | succ j =>
      change formNormSq g.form (codifferentialRealForm g.form (multiplyRealForm η A)) y +
        formNormSq g.form (exteriorRealForm (multiplyRealForm η A)) y = _
      rw [codifferential_cutoff_energy g μ hμ η hη A hA y,
        exterior_cutoff_energy g.form η hη A hA y]
      have h := cutoffErrors_normSq g μ hμ η hη A hA y
      change _ = (formInner g.form (codifferentialRealForm g.form A)
        (codifferentialRealForm g.form (multiplyRealForm (fun t => η t * η t) A)) y +
        formInner g.form (exteriorRealForm A) (exteriorRealForm (multiplyRealForm (fun t => η t * η t) A)) y) + _
      linarith

theorem hodgeEnergyDensity_integrable (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A B : RealForm M k)
    (hA : SmoothRealForm A) (hB : SmoothRealForm B) (hcA : CompactlySupportedRealForm A) :
    Integrable (hodgeEnergyDensity g.form k A B) μ := by
  cases k with
  | zero =>
      exact smooth_compact_formInner_integrable g μ hμ _ _
        (exteriorRealForm_smooth A hA) (exteriorRealForm_smooth B hB)
        (exteriorRealForm_compactlySupported A hA hcA)
  | succ j =>
      exact (smooth_compact_formInner_integrable g μ hμ _ _
        (codifferentialRealForm_smooth g μ hμ A hA) (codifferentialRealForm_smooth g μ hμ B hB)
        (codifferentialRealForm_compactlySupported g μ hμ A hA hcA)).add
        (smooth_compact_formInner_integrable g μ hμ _ _
          (exteriorRealForm_smooth A hA) (exteriorRealForm_smooth B hB)
          (exteriorRealForm_compactlySupported A hA hcA))

theorem integral_hodgeEnergyDensity (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A B : RealForm M k)
    (hA : SmoothRealForm A) (hB : SmoothRealForm B)
    (hcA : CompactlySupportedRealForm A) (hcB : CompactlySupportedRealForm B) :
    (∫ y, hodgeEnergyDensity g.form k A B y ∂μ) =
      ∫ y, formInner g.form (hodgeRealForm g.form k A) B y ∂μ := by
  cases k with
  | zero => exact (integral_hodgeRealForm_zero_energy g μ hμ A B hA hB hcB).symm
  | succ j =>
      rw [integral_hodgeRealForm_succ_energy g μ hμ A B hA hB hcA hcB]
      exact integral_add
        (smooth_compact_formInner_integrable g μ hμ _ _
          (codifferentialRealForm_smooth g μ hμ A hA) (codifferentialRealForm_smooth g μ hμ B hB)
          (codifferentialRealForm_compactlySupported g μ hμ A hA hcA))
        (smooth_compact_formInner_integrable g μ hμ _ _
          (exteriorRealForm_smooth A hA) (exteriorRealForm_smooth B hB)
          (exteriorRealForm_compactlySupported A hA hcA))

/-- The exact integrated Hodge cutoff identity against the actual
second-order operator. The error is only scalar first-gradient energy. -/
theorem integral_hodge_cutoff_IMS (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (η : M.Carrier → ℝ) (hη : SmoothFn η)
    (A : RealForm M k) (hA : SmoothRealForm A) (hcA : CompactlySupportedRealForm A) :
    (∫ y, hodgeEnergyDensity g.form k (multiplyRealForm η A) (multiplyRealForm η A) y ∂μ) =
      (∫ y, formInner g.form (hodgeRealForm g.form k A)
        (multiplyRealForm (fun t => η t * η t) A) y ∂μ) +
      ∫ y, L18Aux.scalarGradientPair g.form η η y * formNormSq g.form A y ∂μ := by
  have hηA := smoothRealForm_multiply η A hη hA
  have hcηA := compactlySupportedRealForm_multiply η A hcA
  have hηsq : SmoothFn (fun t => η t * η t) := fun x => (hη x).mul (hη x)
  have hηsqA := smoothRealForm_multiply (fun t => η t * η t) A hηsq hA
  have hcηsqA := compactlySupportedRealForm_multiply (fun t => η t * η t) A hcA
  have hleft := hodgeEnergyDensity_integrable g μ hμ _ _ hηA hηA hcηA
  have hright := hodgeEnergyDensity_integrable g μ hμ _ _ hA hηsqA hcA
  have hgrad : Integrable (fun y => L18Aux.scalarGradientPair g.form η η y * formNormSq g.form A y) μ := by
    apply (hleft.sub hright).congr
    exact Filter.Eventually.of_forall fun y => by
      change hodgeEnergyDensity g.form k (multiplyRealForm η A) (multiplyRealForm η A) y -
        hodgeEnergyDensity g.form k A (multiplyRealForm (fun t => η t * η t) A) y = _
      rw [hodgeEnergyDensity_cutoff g μ hμ η hη A hA y]
      ring
  calc
    _ = ∫ y, hodgeEnergyDensity g.form k A (multiplyRealForm (fun t => η t * η t) A) y +
        L18Aux.scalarGradientPair g.form η η y * formNormSq g.form A y ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall fun y => hodgeEnergyDensity_cutoff g μ hμ η hη A hA y)
    _ = _ := by rw [integral_add hright hgrad, integral_hodgeEnergyDensity g μ hμ A _ hA hηsqA hcA hcηsqA]

end Yau.LeafProofs.L03
