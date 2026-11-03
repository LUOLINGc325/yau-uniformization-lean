import Yau.LeafProofs.L03HodgeGlobalEnergyApprox

open MeasureTheory Filter
open scoped Topology InnerProductSpace

noncomputable section

namespace Yau.LeafProofs.L03

variable {n k : ℕ} {M : ComplexManifold n}

def realizeActualForm (g : SmoothMetric M) (μ : Measure M.Carrier)
    (A : RealForm M k) (hA : L2RealForm g.form μ A) : L2FormHilbert g μ k :=
  realizeL2Form g μ (L2FormSpace.ofSection A hA)

theorem realizeActualForm_sub (g : SmoothMetric M) (μ : Measure M.Carrier)
    (A B : RealForm M k) (hA : L2RealForm g.form μ A) (hB : L2RealForm g.form μ B) :
    realizeActualForm g μ (A - B) (l2RealForm_sub g μ A B hA hB) =
      realizeActualForm g μ A hA - realizeActualForm g μ B hB := by
  exact realizeL2Form_sub g μ (L2FormSpace.ofSection A hA) (L2FormSpace.ofSection B hB)

theorem realizeActualForm_add (g : SmoothMetric M) (μ : Measure M.Carrier)
    (A B : RealForm M k) (hA : L2RealForm g.form μ A) (hB : L2RealForm g.form μ B) :
    realizeActualForm g μ (A + B) (l2RealForm_add g μ A B hA hB) =
      realizeActualForm g μ A hA + realizeActualForm g μ B hB := by
  exact UniformSpace.Completion.coe_add (L2FormSpace.ofSection A hA) (L2FormSpace.ofSection B hB)

theorem realizeActualForm_norm_sq (g : SmoothMetric M) (μ : Measure M.Carrier)
    (A : RealForm M k) (hA : L2RealForm g.form μ A) :
    ‖realizeActualForm g μ A hA‖ ^ 2 = ∫ y, formNormSq g.form A y ∂μ :=
  realizeL2Form_norm_sq g μ (L2FormSpace.ofSection A hA)

theorem exteriorRealForm_sub (A B : RealForm M k)
    (hA : SmoothRealForm A) (hB : SmoothRealForm B) :
    exteriorRealForm (A - B) = exteriorRealForm A - exteriorRealForm B := by
  rw [sub_eq_add_neg, ← neg_one_smul ℝ B, exteriorRealForm_add A ((-1 : ℝ) • B) hA
    (smoothRealForm_smul (-1) B hB), exteriorRealForm_smul (-1) B hB, neg_one_smul ℝ (exteriorRealForm B),
    ← sub_eq_add_neg]

theorem hodgeLowerRealForm_sub (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A B : RealForm M k)
    (hA : SmoothRealForm A) (hB : SmoothRealForm B) :
    hodgeLowerRealForm g.form k (A - B) =
      hodgeLowerRealForm g.form k A - hodgeLowerRealForm g.form k B := by
  cases k with
  | zero => simp [hodgeLowerRealForm]
  | succ j =>
      change codifferentialRealForm g.form (A - B) = _
      rw [sub_eq_add_neg, ← neg_one_smul ℝ B,
        codifferentialRealForm_add g μ hμ A ((-1 : ℝ) • B) hA (smoothRealForm_smul (-1) B hB),
        codifferentialRealForm_smul g μ hμ (-1) B hB, neg_one_smul ℝ (codifferentialRealForm g.form B)]
      rfl

def hodgeLowerCutoffError (g : HermitianField M) (η : M.Carrier → ℝ)
    (A : RealForm M k) : RealForm M (k - 1) :=
  hodgeLowerRealForm g k (multiplyRealForm η A) -
    multiplyRealForm η (hodgeLowerRealForm g k A)

theorem hodgeLowerCutoffError_normSq_le (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (η : M.Carrier → ℝ) (hη : SmoothFn η)
    (A : RealForm M k) (hA : SmoothRealForm A) (y : M.Carrier) :
    formNormSq g.form (hodgeLowerCutoffError g.form η A) y ≤
      L18Aux.scalarGradientPair g.form η η y * formNormSq g.form A y := by
  cases k with
  | zero =>
      have he : hodgeLowerCutoffError g.form η A = 0 := by
        funext y
        change (0 : (TangentVector M y)[⋀^Fin 0]→L[ℝ] ℝ) - η y • 0 = 0
        simp
      rw [he, formNormSq_zero]
      exact mul_nonneg (L18Aux.scalarGradientPair_self_nonneg g.form η y) (formNormSq_nonneg g.form A y)
  | succ j => exact codifferentialCutoffError_normSq_le g μ hμ η hη A hA y

/-- Physical first-gradient control of a cutoff error gives its actual
Hilbert norm estimate. No second derivative of the cutoff enters. -/
theorem realizeActualForm_norm_le_of_normSq (g : SmoothMetric M) (μ : Measure M.Carrier)
    (A : RealForm M k) {l : ℕ} (E : RealForm M l)
    (hA : L2RealForm g.form μ A) (hE : L2RealForm g.form μ E)
    (γ : ℝ) (hγ : 0 ≤ γ)
    (he : ∀ y, formNormSq g.form E y ≤ γ ^ 2 * formNormSq g.form A y) :
    ‖realizeActualForm g μ E hE‖ ≤ γ * ‖realizeActualForm g μ A hA‖ := by
  have hi := integral_mono (formNormSq_integrable g μ E hE)
    ((formNormSq_integrable g μ A hA).const_mul (γ ^ 2)) he
  rw [integral_const_mul, ← realizeActualForm_norm_sq, ← realizeActualForm_norm_sq] at hi
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hγ (norm_nonneg _))).mp
  simpa only [mul_pow] using hi

theorem realizeActualForm_multiply_norm_le (g : SmoothMetric M) (μ : Measure M.Carrier)
    (η : M.Carrier → ℝ) (hηm : AEStronglyMeasurable η μ)
    (C : ℝ) (hC : 0 ≤ C) (hη : ∀ y, |η y| ≤ C)
    (A : RealForm M k) (hA : L2RealForm g.form μ A) :
    ‖realizeActualForm g μ (multiplyRealForm η A)
      (l2RealForm_multiply_bounded g μ η hηm C hC hη A hA)‖ ≤
      C * ‖realizeActualForm g μ A hA‖ :=
  realizeActualForm_norm_le_of_normSq g μ A _ hA _ C hC
    (multiplyRealForm_normSq_le g.form η A C hC hη)

/-- A pointwise symbol estimate bounds the actual differential of a
scalar multiple in the Hilbert graph norm. -/
theorem realizeActualForm_cutoff_graph_bound (g : SmoothMetric M) (μ : Measure M.Carrier)
    {l : ℕ} (P : RealForm M k → RealForm M l)
    (η : M.Carrier → ℝ) (hηm : AEStronglyMeasurable η μ)
    (C γ : ℝ) (hC : 0 ≤ C) (hγ : 0 ≤ γ) (hη : ∀ y, |η y| ≤ C)
    (A : RealForm M k) (hA : L2RealForm g.form μ A)
    (hPA : L2RealForm g.form μ (P A)) (hPηA : L2RealForm g.form μ (P (multiplyRealForm η A)))
    (he : ∀ y, formNormSq g.form (P (multiplyRealForm η A) - multiplyRealForm η (P A)) y ≤
      γ ^ 2 * formNormSq g.form A y) :
    ‖realizeActualForm g μ (P (multiplyRealForm η A)) hPηA‖ ≤
      C * ‖realizeActualForm g μ (P A) hPA‖ + γ * ‖realizeActualForm g μ A hA‖ := by
  let V := multiplyRealForm η (P A)
  have hV : L2RealForm g.form μ V := l2RealForm_multiply_bounded g μ η hηm C hC hη _ hPA
  let E := P (multiplyRealForm η A) - V
  have hE : L2RealForm g.form μ E := l2RealForm_sub g μ _ _ hPηA hV
  have hnormE := realizeActualForm_norm_le_of_normSq g μ A E hA hE γ hγ he
  have hnormV := realizeActualForm_multiply_norm_le g μ η hηm C hC hη (P A) hPA
  have hsum : realizeActualForm g μ (P (multiplyRealForm η A)) hPηA =
      realizeActualForm g μ V hV + realizeActualForm g μ E hE := by
    rw [← realizeActualForm_add]
    congr 1
    dsimp only [E]
    abel
  rw [hsum]
  exact (norm_add_le _ _).trans (add_le_add hnormV hnormE)

theorem exterior_cutoff_graph_norm_le (g : SmoothMetric M) (μ : Measure M.Carrier)
    (η : M.Carrier → ℝ) (hη : SmoothFn η)
    (C γ : ℝ) (hC : 0 ≤ C) (hγ : 0 ≤ γ) (hηb : ∀ y, |η y| ≤ C)
    (hgrad : ∀ y, L18Aux.scalarGradientPair g.form η η y ≤ γ ^ 2)
    (A : RealForm M k) (hAs : SmoothRealForm A) (hA : L2RealForm g.form μ A)
    (hdA : L2RealForm g.form μ (exteriorRealForm A))
    (hdηA : L2RealForm g.form μ (exteriorRealForm (multiplyRealForm η A))) :
    ‖realizeActualForm g μ (exteriorRealForm (multiplyRealForm η A)) hdηA‖ ≤
      C * ‖realizeActualForm g μ (exteriorRealForm A) hdA‖ + γ * ‖realizeActualForm g μ A hA‖ := by
  apply realizeActualForm_cutoff_graph_bound g μ exteriorRealForm η
    (L18Aux.continuous_of_smoothFn hη).aestronglyMeasurable C γ hC hγ hηb A hA hdA hdηA
  intro y
  exact (exteriorCutoffError_normSq_le g.form η hη A hAs y).trans
    (mul_le_mul_of_nonneg_right (hgrad y) (formNormSq_nonneg g.form A y))

theorem hodgeLower_cutoff_graph_norm_le (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (η : M.Carrier → ℝ) (hη : SmoothFn η)
    (C γ : ℝ) (hC : 0 ≤ C) (hγ : 0 ≤ γ) (hηb : ∀ y, |η y| ≤ C)
    (hgrad : ∀ y, L18Aux.scalarGradientPair g.form η η y ≤ γ ^ 2)
    (A : RealForm M k) (hAs : SmoothRealForm A) (hA : L2RealForm g.form μ A)
    (hlA : L2RealForm g.form μ (hodgeLowerRealForm g.form k A))
    (hlηA : L2RealForm g.form μ (hodgeLowerRealForm g.form k (multiplyRealForm η A))) :
    ‖realizeActualForm g μ (hodgeLowerRealForm g.form k (multiplyRealForm η A)) hlηA‖ ≤
      C * ‖realizeActualForm g μ (hodgeLowerRealForm g.form k A) hlA‖ + γ * ‖realizeActualForm g μ A hA‖ := by
  apply realizeActualForm_cutoff_graph_bound g μ (hodgeLowerRealForm g.form k) η
    (L18Aux.continuous_of_smoothFn hη).aestronglyMeasurable C γ hC hγ hηb A hA hlA hlηA
  intro y
  exact (hodgeLowerCutoffError_normSq_le g μ hμ η hη A hAs y).trans
    (mul_le_mul_of_nonneg_right (hgrad y) (formNormSq_nonneg g.form A y))

theorem exists_compact_cutoff_uniform_bounds (g : SmoothMetric M)
    (η : M.Carrier → ℝ) (hη : SmoothFn η) (hcη : HasCompactSupport η) :
    ∃ C γ : ℝ, 0 ≤ C ∧ 0 ≤ γ ∧ (∀ y, |η y| ≤ C) ∧
      ∀ y, L18Aux.scalarGradientPair g.form η η y ≤ γ ^ 2 := by
  obtain ⟨C, hC⟩ := (L18Aux.continuous_of_smoothFn hη).bounded_above_of_compact_support hcη
  obtain ⟨D, hD⟩ := (L18Aux.continuous_of_smoothFn
    (L18Aux.smoothFn_scalarGradientPair g hη hη)).bounded_above_of_compact_support
      (L18Aux.scalarGradientPair_hasCompactSupport g.form η η hcη)
  refine ⟨max C 0, Real.sqrt (max D 0), le_max_right _ _, Real.sqrt_nonneg _, ?_, ?_⟩
  · intro y
    exact (show |η y| ≤ C by simpa only [Real.norm_eq_abs] using hC y).trans (le_max_left _ _)
  · intro y
    rw [Real.sq_sqrt (le_max_right _ _)]
    exact (le_abs_self _).trans ((show |L18Aux.scalarGradientPair g.form η η y| ≤ D by
      simpa only [Real.norm_eq_abs] using hD y).trans (le_max_left _ _))

end Yau.LeafProofs.L03
