import Yau.LeafProofs.L03DiracCutoffPairing

open MeasureTheory Filter
open scoped Topology ContDiff

noncomputable section

namespace Yau.LeafProofs.L03

variable {n k : ℕ} {M : ComplexManifold n}

theorem modelFormInner_self_nonneg (g : HermitianField M) (x : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget x)
    (P : (ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ) :
    0 ≤ modelFormInner (realMetricFn g x z)⁻¹ P P := by
  by_cases hP : P = 0
  · simp only [hP, modelFormInner_zero_left]
    exact le_rfl
  · exact (modelFormInner_self_pos g x hz P hP).le

theorem modelFormInner_neg_self (B : Matrix (RIdx n) (RIdx n) ℝ)
    (P : (ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ) :
    modelFormInner B (-P) (-P) = modelFormInner B P P := by
  simp only [modelFormInner, tensorCoefficientPairing, ContinuousAlternatingMap.neg_apply,
    neg_mul, mul_neg, neg_neg]

def exteriorCutoffError (η : M.Carrier → ℝ) (A : RealForm M k) : RealForm M (k + 1) :=
  exteriorRealForm (multiplyRealForm η A) - multiplyRealForm η (exteriorRealForm A)

def codifferentialCutoffError (g : HermitianField M) (η : M.Carrier → ℝ)
    (A : RealForm M (k + 1)) : RealForm M k :=
  codifferentialRealForm g (multiplyRealForm η A) - multiplyRealForm η (codifferentialRealForm g A)

/-- The actual exterior cutoff commutator has precisely the exterior
Clifford symbol in every genuine chart. -/
theorem exteriorCutoffError_to_chart (η : M.Carrier → ℝ) (hη : SmoothFn η)
    (A : RealForm M k) (hA : SmoothRealForm A) (x : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget x) :
    chartForm (exteriorCutoffError η A) x z =
      modelExteriorSymbol (fderiv ℝ (inChart x η) z) (chartForm A x z) := by
  apply modelFormCoefficientMap_injective n (k + 1)
  funext I
  change formComponents (exteriorRealForm (multiplyRealForm η A)) x z I -
      formComponents (multiplyRealForm η (exteriorRealForm A)) x z I = _
  rw [formComponents_multiplyRealForm,
    exteriorRealForm_represents (multiplyRealForm η A) (smoothRealForm_multiply η A hη hA) x z hz I,
    exteriorRealForm_represents A hA x z hz I]
  have hm : formComponents (multiplyRealForm η A) x =
      (fun w J => inChart x η w * formComponents A x w J) := by
    funext w J
    exact formComponents_multiplyRealForm η A x w J
  rw [hm, exteriorComponents_multiply_modelSymbol (inChart x η) A x z
    (((hη x).contDiffAt ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).differentiableAt (by simp))
    (smoothRealForm_coefficient_differentiableAt A hA x hz) I]
  ring_nf; rfl

/-- The actual codifferential cutoff commutator has the negative metric
contraction symbol in every genuine chart. -/
theorem codifferentialCutoffError_to_chart (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (η : M.Carrier → ℝ) (hη : SmoothFn η)
    (A : RealForm M (k + 1)) (hA : SmoothRealForm A) (x : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget x) :
    chartForm (codifferentialCutoffError g.form η A) x z =
      -((chartForm A x z).curryLeft
        (modelMetricSharp (realMetricFn g.form x z)⁻¹ (fderiv ℝ (inChart x η) z))) := by
  apply modelFormCoefficientMap_injective n k
  funext I
  change formComponents (codifferentialRealForm g.form (multiplyRealForm η A)) x z I -
      formComponents (multiplyRealForm η (codifferentialRealForm g.form A)) x z I = _
  rw [formComponents_multiplyRealForm,
    codifferentialRealForm_represents g μ hμ (multiplyRealForm η A) (smoothRealForm_multiply η A hη hA) x z hz I,
    codifferentialRealForm_represents g μ hμ A hA x z hz I]
  have hm : formComponents (multiplyRealForm η A) x =
      (fun w J => inChart x η w * formComponents A x w J) := by
    funext w J
    exact formComponents_multiplyRealForm η A x w J
  rw [hm, codifferentialComponents_multiply_modelSymbol g.form (inChart x η) A x z
    (((hη x).contDiffAt ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).differentiableAt (by simp))
    (smoothRealForm_coefficient_differentiableAt A hA x hz) I]
  change _ = -_
  ring_nf; rfl

/-- Pointwise physical-gradient control of the actual exterior cutoff
error, in the frozen metric norm. -/
theorem exteriorCutoffError_normSq_le (g : HermitianField M) (η : M.Carrier → ℝ)
    (hη : SmoothFn η) (A : RealForm M k) (hA : SmoothRealForm A) (y : M.Carrier) :
    formNormSq g (exteriorCutoffError η A) y ≤
      L18Aux.scalarGradientPair g η η y * formNormSq g A y := by
  let z := chartPt y y
  have hz : z ∈ chartTarget y := mem_extChartAt_target y
  have hi : chartInv y z = y := (extChartAt (ComplexModel n) y).left_inv (mem_extChartAt_source y)
  have he := exteriorCutoffError_to_chart η hη A hA y hz
  have hn := modelFormInner_chartForm g (exteriorCutoffError η A) (exteriorCutoffError η A) y hz
  simp only [he, hi] at hn
  change _ = formNormSq g (exteriorCutoffError η A) y at hn
  rw [← hn]
  cases k with
  | zero =>
      have h := actual_symbol_energy_zero g A hη y hz
      dsimp only at h
      rw [hi] at h
      exact h.le
  | succ j =>
      have h := actual_symbol_energy g A hη y hz
      dsimp only at h
      rw [hi] at h
      have hp := modelFormInner_self_nonneg g y hz
        ((chartForm A y z).curryLeft (modelMetricSharp (realMetricFn g y z)⁻¹ (fderiv ℝ (inChart y η) z)))
      linarith

/-- Pointwise physical-gradient control of the actual codifferential
cutoff error in the same frozen metric norm. -/
theorem codifferentialCutoffError_normSq_le (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (η : M.Carrier → ℝ) (hη : SmoothFn η)
    (A : RealForm M (k + 1)) (hA : SmoothRealForm A) (y : M.Carrier) :
    formNormSq g.form (codifferentialCutoffError g.form η A) y ≤
      L18Aux.scalarGradientPair g.form η η y * formNormSq g.form A y := by
  let z := chartPt y y
  have hz : z ∈ chartTarget y := mem_extChartAt_target y
  have hi : chartInv y z = y := (extChartAt (ComplexModel n) y).left_inv (mem_extChartAt_source y)
  have he := codifferentialCutoffError_to_chart g μ hμ η hη A hA y hz
  have hn := modelFormInner_chartForm g.form (codifferentialCutoffError g.form η A)
    (codifferentialCutoffError g.form η A) y hz
  simp only [he, modelFormInner_neg_self, hi] at hn
  change _ = formNormSq g.form (codifferentialCutoffError g.form η A) y at hn
  rw [← hn]
  have h := actual_symbol_energy g.form A hη y hz
  dsimp only at h
  rw [hi] at h
  have hp := modelFormInner_self_nonneg g.form y hz
    (modelExteriorSymbol (fderiv ℝ (inChart y η) z) (chartForm A y z))
  linarith

theorem gradedInner_self_nonneg (g : HermitianField M)
    (B : OperatorCandidates.GradedRealForm M) (y : M.Carrier) :
    0 ≤ OperatorCandidates.gradedInner g B B y :=
  Finset.sum_nonneg (fun _ _ => formNormSq_nonneg g _ y)

theorem formNormSq_le_gradedInner_self (g : HermitianField M)
    (B : OperatorCandidates.GradedRealForm M) (j : ℕ) (y : M.Carrier) :
    formNormSq g (B j) y ≤ OperatorCandidates.gradedInner g B B y := by
  by_cases hj : j < 2 * n + 1
  · exact Finset.single_le_sum (fun i _ => formNormSq_nonneg g (B i.val) y)
      (Finset.mem_univ (⟨j, hj⟩ : Fin (2 * n + 1)))
  · rw [realForm_eq_zero_of_degree_gt (B j) (by omega), formNormSq_zero]
    exact gradedInner_self_nonneg g B y

theorem diracCutoffCommutator_zero (g : HermitianField M) (η : M.Carrier → ℝ)
    (B : OperatorCandidates.GradedRealForm M) :
    diracCutoffCommutator g η B 0 = codifferentialCutoffError g η (B 1) := rfl

theorem diracCutoffCommutator_succ (g : HermitianField M) (η : M.Carrier → ℝ)
    (B : OperatorCandidates.GradedRealForm M) (j : ℕ) :
    diracCutoffCommutator g η B (j + 1) =
      exteriorCutoffError η (B j) + codifferentialCutoffError g η (B (j + 2)) := by
  funext y
  simp only [diracCutoffCommutator, diracRealForm, multiplyGradedForm,
    exteriorCutoffError, codifferentialCutoffError, multiplyRealForm,
    Pi.sub_apply, Pi.add_apply, smul_add]
  abel

/-- A dimensional physical-gradient bound for each actual graded
commutator component. It also covers the top degree and dimension zero. -/
theorem diracCutoffCommutator_component_normSq_le (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (η : M.Carrier → ℝ) (hη : SmoothFn η)
    (B : OperatorCandidates.GradedRealForm M) (hB : ∀ j, SmoothRealForm (B j))
    (j : ℕ) (y : M.Carrier) :
    formNormSq g.form (diracCutoffCommutator g.form η B j) y ≤
      4 * L18Aux.scalarGradientPair g.form η η y * OperatorCandidates.gradedInner g.form B B y := by
  have hgrad := L18Aux.scalarGradientPair_self_nonneg g.form η y
  have henergy := gradedInner_self_nonneg g.form B y
  have hbound (i : ℕ) := mul_le_mul_of_nonneg_left
    (formNormSq_le_gradedInner_self g.form B i y) hgrad
  cases j with
  | zero =>
      rw [diracCutoffCommutator_zero]
      have h := (codifferentialCutoffError_normSq_le g μ hμ η hη (B 1) (hB 1) y).trans (hbound 1)
      nlinarith [mul_nonneg hgrad henergy]
  | succ j =>
      rw [diracCutoffCommutator_succ]
      have ha := formNormSq_add_le g.form (exteriorCutoffError η (B j))
        (codifferentialCutoffError g.form η (B (j + 2))) y
      have he := (exteriorCutoffError_normSq_le g.form η hη (B j) (hB j) y).trans (hbound j)
      have hd := (codifferentialCutoffError_normSq_le g μ hμ η hη (B (j + 2)) (hB (j + 2)) y).trans (hbound (j + 2))
      linarith

/-- The computed full Dirac commutator is uniformly controlled by the
physical scalar gradient, with a constant depending only on dimension. -/
theorem diracCutoffCommutator_graded_normSq_le (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (η : M.Carrier → ℝ) (hη : SmoothFn η)
    (B : OperatorCandidates.GradedRealForm M) (hB : ∀ j, SmoothRealForm (B j))
    (y : M.Carrier) :
    OperatorCandidates.gradedInner g.form (diracCutoffCommutator g.form η B)
        (diracCutoffCommutator g.form η B) y ≤
      (4 * (2 * n + 1 : ℕ) : ℝ) * L18Aux.scalarGradientPair g.form η η y *
        OperatorCandidates.gradedInner g.form B B y := by
  calc
    _ ≤ ∑ j : Fin (2 * n + 1), 4 * L18Aux.scalarGradientPair g.form η η y *
        OperatorCandidates.gradedInner g.form B B y :=
      Finset.sum_le_sum (fun j _ => diracCutoffCommutator_component_normSq_le g μ hμ η hη B hB j.val y)
    _ = _ := by simp; ring

end Yau.LeafProofs.L03
