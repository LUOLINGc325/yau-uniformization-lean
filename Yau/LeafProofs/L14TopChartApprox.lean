import Yau.LeafProofs.L14TopChartPush
import Yau.LeafProofs.L14CompactLpFields

set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped Manifold Topology ContDiff ComplexOrder ENNReal Matrix
open MeasureTheory Bundle Filter Module
namespace Yau.LeafProofs.L14Aux
open BundleDbar
variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

theorem formNormSq_multiply_real_top (g : HermitianField M) (h : Metric E)
    (χ : M.Carrier → ℝ) (u : NQForm E 0) (x : M.Carrier) :
    BundleDbar.formNormSq (r := r) E g h (multiplyForm E (fun x => (χ x : ℂ)) u) x =
      χ x ^ 2 * BundleDbar.formNormSq (r := r) E g h u x := by
  have he : multiplyForm E (fun x => (χ x : ℂ)) u x = ((χ x : ℂ) • u) x := by
    apply Subtype.ext
    rfl
  rw [formNormSq_congr_at E g h _ _ x he, formNormSq_top_smul]
  simp only [Complex.normSq_ofReal, pow_two]

theorem weightedL2_multiply_real_top (g : HermitianField M) (μ : Measure M.Carrier)
    (h : Metric E) (φ : M.Carrier → ℝ) (χ : M.Carrier → ℝ) (hχ : SmoothFn χ)
    (u : NQForm E 0) (hu : WeightedL2 (r := r) E g h μ φ u)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ x, χ x ^ 2 ≤ C) :
    WeightedL2 (r := r) E g h μ φ (multiplyForm E (fun x => (χ x : ℂ)) u) := by
  have hη (a : M.Carrier) : ContinuousOn (inChart a (fun x => (χ x : ℂ))) (localDomain (r := r) E a) :=
    (((hχ a).continuousLinearMap_comp Complex.ofRealCLM).continuousOn.mono Set.inter_subset_left)
  refine ⟨locallyL2_multiplyForm E (fun x => (χ x : ℂ)) hη u hu.1, ?_⟩
  have hn (x : M.Carrier) : 0 ≤ BundleDbar.formNormSq (r := r) E g h u x * Real.exp (-φ x) :=
    mul_nonneg (formNormSq_top_nonneg E g h u x) (Real.exp_pos _).le
  have hle : weightedNormSq (r := r) E g h μ φ (multiplyForm E (fun x => (χ x : ℂ)) u) ≤
      ENNReal.ofReal C * weightedNormSq (r := r) E g h μ φ u := by
    calc
      _ ≤ ∫⁻ x, ENNReal.ofReal (C * (BundleDbar.formNormSq (r := r) E g h u x * Real.exp (-φ x))) ∂μ := by
        apply lintegral_mono
        intro x
        change ENNReal.ofReal (BundleDbar.formNormSq (r := r) E g h
          (multiplyForm E (fun x => (χ x : ℂ)) u) x * Real.exp (-φ x)) ≤ _
        rw [formNormSq_multiply_real_top]
        apply ENNReal.ofReal_le_ofReal
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hbound x) (hn x)
      _ = _ := by
        simp only [ENNReal.ofReal_mul hC]
        exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  exact hle.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hu.2)

variable (g : Yau.SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
  (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)

def weightedTopCutoffSection (χ : M.Carrier → ℝ) (hχ : SmoothFn χ)
    (hbound : ∀ x, χ x ∈ Set.Icc (0 : ℝ) 1) (U : WeightedTopSection E g μ hμ h hh φ hφ) :
    WeightedTopSection E g μ hμ h hh φ hφ :=
  ⟨multiplyForm E (fun x => (χ x : ℂ)) U.1,
    weightedL2_multiply_real_top E g.form μ h φ χ hχ U.1 U.2 1 (by norm_num)
      (fun x => by have h0 := (hbound x).1; have h1 := (hbound x).2; nlinarith)⟩

/-- Multiplication by an arbitrary smooth, uniformly bounded real function. -/
def weightedTopMultiplierSection (χ : M.Carrier → ℝ) (hχ : SmoothFn χ)
    (C : ℝ) (_hC : 0 ≤ C) (hbound : ∀ x, χ x ^ 2 ≤ C ^ 2)
    (U : WeightedTopSection E g μ hμ h hh φ hφ) :
    WeightedTopSection E g μ hμ h hh φ hφ :=
  ⟨multiplyForm E (fun x => (χ x : ℂ)) U.1,
    weightedL2_multiply_real_top E g.form μ h φ χ hχ U.1 U.2 (C ^ 2)
      (sq_nonneg C) hbound⟩

@[simp] theorem weightedTopCutoffSection_toForm (χ : M.Carrier → ℝ) (hχ : SmoothFn χ)
    (hbound : ∀ x, χ x ∈ Set.Icc (0 : ℝ) 1)
    (U : WeightedTopSection E g μ hμ h hh φ hφ) :
    (weightedTopCutoffSection E g μ hμ h hh φ hφ χ hχ hbound U).toForm E g μ hμ h hh φ hφ =
      multiplyForm E (fun x => (χ x : ℂ)) (U.toForm E g μ hμ h hh φ hφ) := rfl

@[simp] theorem weightedTopMultiplierSection_toForm (χ : M.Carrier → ℝ) (hχ : SmoothFn χ)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ x, χ x ^ 2 ≤ C ^ 2)
    (U : WeightedTopSection E g μ hμ h hh φ hφ) :
    (weightedTopMultiplierSection E g μ hμ h hh φ hφ χ hχ C hC hbound U).toForm E g μ hμ h hh φ hφ =
      multiplyForm E (fun x => (χ x : ℂ)) (U.toForm E g μ hμ h hh φ hφ) := rfl

theorem weightedTopMultiplierSection_norm_le (χ : M.Carrier → ℝ) (hχ : SmoothFn χ)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ x, χ x ^ 2 ≤ C ^ 2)
    (U : WeightedTopSection E g μ hμ h hh φ hφ) :
    ‖weightedTopMultiplierSection E g μ hμ h hh φ hφ χ hχ C hC hbound U‖ ≤ C * ‖U‖ := by
  let V := weightedTopMultiplierSection E g μ hμ h hh φ hφ χ hχ C hC hbound U
  have hle : weightedNormSq (r := r) E g.form h μ φ V.1 ≤
      ENNReal.ofReal (C ^ 2) * weightedNormSq (r := r) E g.form h μ φ U.1 := by
    calc
      _ ≤ ∫⁻ x, ENNReal.ofReal (C ^ 2 *
          (BundleDbar.formNormSq (r := r) E g.form h U.1 x * Real.exp (-φ x))) ∂μ := by
        apply lintegral_mono
        intro x
        change ENNReal.ofReal (BundleDbar.formNormSq (r := r) E g.form h
          (multiplyForm E (fun x => (χ x : ℂ)) U.1) x * Real.exp (-φ x)) ≤ _
        rw [formNormSq_multiply_real_top]
        apply ENNReal.ofReal_le_ofReal
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hbound x)
          (mul_nonneg (formNormSq_top_nonneg E g.form h U.1 x) (Real.exp_pos _).le)
      _ = _ := by
        simp only [ENNReal.ofReal_mul (sq_nonneg C)]
        exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have hreal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top U.2.2.ne) hle
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg C)] at hreal
  have hV := weightedTopSection_norm_sq E g μ hμ h hh φ hφ V
  have hU := weightedTopSection_norm_sq E g μ hμ h hh φ hφ U
  change ‖V‖ ^ 2 = (weightedNormSq (r := r) E g.form h μ φ V.1).toReal at hV
  change ‖U‖ ^ 2 = (weightedNormSq (r := r) E g.form h μ φ U.1).toReal at hU
  rw [← hV, ← hU] at hreal
  change ‖V‖ ≤ C * ‖U‖
  nlinarith [norm_nonneg V, norm_nonneg U, mul_nonneg hC (norm_nonneg U)]

def weightedTopMultiplierLinearMap (χ : M.Carrier → ℝ) (hχ : SmoothFn χ)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ x, χ x ^ 2 ≤ C ^ 2) :
    WeightedTopSection E g μ hμ h hh φ hφ →ₗ[ℂ]
      WeightedTopSection E g μ hμ h hh φ hφ where
  toFun := weightedTopMultiplierSection E g μ hμ h hh φ hφ χ hχ C hC hbound
  map_add' U V := by
    apply Subtype.ext
    funext x
    apply Subtype.ext
    exact smul_add (χ x : ℂ) (U.1 x).1 (V.1 x).1
  map_smul' c U := by
    apply Subtype.ext
    funext x
    apply Subtype.ext
    exact smul_comm (χ x : ℂ) c (U.1 x).1

def weightedTopMultiplierRaw (χ : M.Carrier → ℝ) (hχ : SmoothFn χ)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ x, χ x ^ 2 ≤ C ^ 2) :
    WeightedTopSection E g μ hμ h hh φ hφ →L[ℂ]
      WeightedTopSection E g μ hμ h hh φ hφ :=
  (weightedTopMultiplierLinearMap E g μ hμ h hh φ hφ χ hχ C hC hbound).mkContinuous C
    (weightedTopMultiplierSection_norm_le E g μ hμ h hh φ hφ χ hχ C hC hbound)

/-- The actual bounded multiplier on the separated completion of weighted top-forms. -/
def weightedTopMultiplier (χ : M.Carrier → ℝ) (hχ : SmoothFn χ)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ x, χ x ^ 2 ≤ C ^ 2) :
    WeightedTopHilbert E g μ hμ h hh φ hφ →L[ℂ]
      WeightedTopHilbert E g μ hμ h hh φ hφ :=
  (weightedTopMultiplierRaw E g μ hμ h hh φ hφ χ hχ C hC hbound).completion

theorem weightedTopMultiplier_realize (χ : M.Carrier → ℝ) (hχ : SmoothFn χ)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ x, χ x ^ 2 ≤ C ^ 2)
    (U : WeightedTopSection E g μ hμ h hh φ hφ) :
    weightedTopMultiplier E g μ hμ h hh φ hφ χ hχ C hC hbound
      (realizeWeightedTopSection E g μ hμ h hh φ hφ U) =
      realizeWeightedTopSection E g μ hμ h hh φ hφ
        (weightedTopMultiplierSection E g μ hμ h hh φ hφ χ hχ C hC hbound U) :=
  ContinuousLinearMap.completion_apply_coe _ U

theorem weightedTopMultiplier_norm_le (χ : M.Carrier → ℝ) (hχ : SmoothFn χ)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ x, χ x ^ 2 ≤ C ^ 2)
    (W : WeightedTopHilbert E g μ hμ h hh φ hφ) :
    ‖weightedTopMultiplier E g μ hμ h hh φ hφ χ hχ C hC hbound W‖ ≤ C * ‖W‖ := by
  induction W using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_le (by fun_prop) (by fun_prop)
  | ih U =>
    change ‖weightedTopMultiplier E g μ hμ h hh φ hφ χ hχ C hC hbound
      (realizeWeightedTopSection E g μ hμ h hh φ hφ U)‖ ≤
      C * ‖realizeWeightedTopSection E g μ hμ h hh φ hφ U‖
    rw [weightedTopMultiplier_realize E g μ hμ h hh φ hφ]
    simpa only [realizeWeightedTopSection, UniformSpace.Completion.norm_coe] using
      weightedTopMultiplierSection_norm_le E g μ hμ h hh φ hφ χ hχ C hC hbound U

theorem weightedTopMultiplier_opNorm_le (χ : M.Carrier → ℝ) (hχ : SmoothFn χ)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ x, χ x ^ 2 ≤ C ^ 2) :
    ‖weightedTopMultiplier E g μ hμ h hh φ hφ χ hχ C hC hbound‖ ≤ C :=
  ContinuousLinearMap.opNorm_le_bound _ hC
    (weightedTopMultiplier_norm_le E g μ hμ h hh φ hφ χ hχ C hC hbound)

/-- A cutoff multiplier is a contraction on the actual Hilbert completion. -/
def weightedTopCutoff (χ : M.Carrier → ℝ) (hχ : SmoothFn χ)
    (hbound : ∀ x, χ x ∈ Set.Icc (0 : ℝ) 1) :
    WeightedTopHilbert E g μ hμ h hh φ hφ →L[ℂ]
      WeightedTopHilbert E g μ hμ h hh φ hφ :=
  weightedTopMultiplier E g μ hμ h hh φ hφ χ hχ 1 zero_le_one
    (fun x => by have h0 := (hbound x).1; have h1 := (hbound x).2; nlinarith)

theorem weightedTopCutoff_realize (χ : M.Carrier → ℝ) (hχ : SmoothFn χ)
    (hbound : ∀ x, χ x ∈ Set.Icc (0 : ℝ) 1)
    (U : WeightedTopSection E g μ hμ h hh φ hφ) :
    weightedTopCutoff E g μ hμ h hh φ hφ χ hχ hbound
      (realizeWeightedTopSection E g μ hμ h hh φ hφ U) =
      realizeWeightedTopSection E g μ hμ h hh φ hφ
        (weightedTopCutoffSection E g μ hμ h hh φ hφ χ hχ hbound U) := by
  exact ContinuousLinearMap.completion_apply_coe _ U

theorem weightedTopCutoff_norm_le (χ : M.Carrier → ℝ) (hχ : SmoothFn χ)
    (hbound : ∀ x, χ x ∈ Set.Icc (0 : ℝ) 1)
    (W : WeightedTopHilbert E g μ hμ h hh φ hφ) :
    ‖weightedTopCutoff E g μ hμ h hh φ hφ χ hχ hbound W‖ ≤ ‖W‖ := by
  exact (one_mul ‖W‖) ▸ weightedTopMultiplier_norm_le E g μ hμ h hh φ hφ χ hχ 1 zero_le_one _ W

theorem weightedTopCutoff_opNorm_le (χ : M.Carrier → ℝ) (hχ : SmoothFn χ)
    (hbound : ∀ x, χ x ∈ Set.Icc (0 : ℝ) 1) :
    ‖weightedTopCutoff E g μ hμ h hh φ hφ χ hχ hbound‖ ≤ 1 :=
  weightedTopMultiplier_opNorm_le E g μ hμ h hh φ hφ χ hχ 1 zero_le_one _


/-- The compact local field of an actual section is its coefficient field,
extended by zero, almost everywhere on the model space. -/
theorem compactTopHilbertField_realize_ae
    (a : M.Carrier) (K : Set (ComplexVector n)) (hK : IsCompact K)
    (hKO : K ⊆ localDomain (r := r) E a)
    (U : WeightedTopSection E g μ hμ h hh φ hφ) (α : Fin r) :
    (fun z => compactTopHilbertField E g μ hμ h hh φ hφ a K hK hKO
      (realizeWeightedTopSection E g μ hμ h hh φ hφ U) z α) =ᵐ[lebesgueC n]
      K.indicator (fun z => coefficients (r := r) E U.1 a z Fin.elim0 α) := by
  exact (ae_eq_restrict_iff_indicator_ae_eq hK.measurableSet).mp
    (weightedTopHilbertLocalCoefficient_realize_ae E g μ hμ h hh φ hφ a K hK hKO α U)

/-- Local coefficients of the actual completed cutoff are scalar multiples
of the original local coefficients. -/
theorem weightedTopHilbertLocalCoefficient_cutoff_ae
    (a : M.Carrier) (K : Set (ComplexVector n)) (hK : IsCompact K)
    (hKO : K ⊆ localDomain (r := r) E a)
    (χ : M.Carrier → ℝ) (hχ : SmoothFn χ)
    (hboundχ : ∀ x, χ x ∈ Set.Icc (0 : ℝ) 1)
    (U : WeightedTopHilbert E g μ hμ h hh φ hφ) (α : Fin r) :
    weightedTopHilbertLocalCoefficient E g μ hμ h hh φ hφ a K hK hKO α
      (weightedTopCutoff E g μ hμ h hh φ hφ χ hχ hboundχ U) =ᵐ[(lebesgueC n).restrict K]
      (fun z => (χ (chartInv a z) : ℂ) *
        weightedTopHilbertLocalCoefficient E g μ hμ h hh φ hφ a K hK hKO α U z) := by
  let V := weightedTopHilbertRepresentative E g μ hμ h hh φ hφ U
  have hV : realizeWeightedTopSection E g μ hμ h hh φ hφ V = U :=
    weightedTopHilbertRepresentative_realize E g μ hμ h hh φ hφ U
  have he := weightedTopHilbertLocalCoefficient_realize_ae E g μ hμ h hh φ hφ a K hK hKO α
    (weightedTopCutoffSection E g μ hμ h hh φ hφ χ hχ hboundχ V)
  rw [← weightedTopCutoff_realize E g μ hμ h hh φ hφ χ hχ hboundχ V, hV] at he
  have hf := weightedTopHilbertLocalCoefficient_realize_ae E g μ hμ h hh φ hφ a K hK hKO α V
  rw [hV] at hf
  filter_upwards [he, hf] with z hez hfz
  rw [hez, hfz]
  exact coefficients_multiplyForm E (fun x => (χ x : ℂ)) V.1 a z Fin.elim0 α

/-- Multiplication by a cutoff commutes with taking the compact local field,
in the ordinary global model-space almost-everywhere sense. -/
theorem compactTopHilbertField_cutoff_ae
    (a : M.Carrier) (K : Set (ComplexVector n)) (hK : IsCompact K)
    (hKO : K ⊆ localDomain (r := r) E a)
    (χ : M.Carrier → ℝ) (hχ : SmoothFn χ)
    (hboundχ : ∀ x, χ x ∈ Set.Icc (0 : ℝ) 1)
    (U : WeightedTopHilbert E g μ hμ h hh φ hφ) (α : Fin r) :
    (fun z => compactTopHilbertField E g μ hμ h hh φ hφ a K hK hKO
      (weightedTopCutoff E g μ hμ h hh φ hφ χ hχ hboundχ U) z α) =ᵐ[lebesgueC n]
      (fun z => (χ (chartInv a z) : ℂ) *
        compactTopHilbertField E g μ hμ h hh φ hφ a K hK hKO U z α) := by
  have he := (ae_eq_restrict_iff_indicator_ae_eq hK.measurableSet).mp
    (weightedTopHilbertLocalCoefficient_cutoff_ae E g μ hμ h hh φ hφ a K hK hKO χ hχ hboundχ U α)
  apply he.trans
  exact Eventually.of_forall fun z => by
    by_cases hz : z ∈ K
    · simp only [compactTopHilbertField, compactLpField, Set.indicator_of_mem hz]
    · simp only [compactTopHilbertField, compactLpField, Set.indicator_of_notMem hz, mul_zero]

/-- Smooth model fields supported in one compact chart approximate the actual
cutoff of every point of the weighted top-form Hilbert completion. -/
theorem weightedTopChartSection_tendsto_cutoff_of_model_errors
    (hE : Holomorphic (r := r) E)
    (a : M.Carrier) (K : Set (ComplexVector n)) (hK : IsCompact K)
    (hKO : K ⊆ localDomain (r := r) E a)
    (χ : M.Carrier → ℝ) (hχ : SmoothFn χ)
    (hboundχ : ∀ x, χ x ∈ Set.Icc (0 : ℝ) 1)
    (hsχ : tsupport χ ⊆ bundleChartSource (r := r) E a)
    (hKχ : tsupport (L18Aux.chartPullbackZero a χ) ⊆ K)
    (U : WeightedTopHilbert E g μ hμ h hh φ hφ)
    (F : ℕ → ComplexVector n → ComplexVector r)
    (hF : ∀ j, ContDiff ℝ ∞ (F j)) (hsF : ∀ j, tsupport (F j) ⊆ K)
    (he : ∀ j α, MemLp
      (fun z => F j z α - compactTopHilbertField E g μ hμ h hh φ hφ a K hK hKO
        (weightedTopCutoff E g μ hμ h hh φ hφ χ hχ hboundχ U) z α) 2 (lebesgueC n))
    (ht : ∀ α, Tendsto (fun j => ∫ z,
      ‖F j z α - compactTopHilbertField E g μ hμ h hh φ hφ a K hK hKO
        (weightedTopCutoff E g μ hμ h hh φ hφ χ hχ hboundχ U) z α‖ ^ 2 ∂lebesgueC n)
      atTop (𝓝 0)) :
    Tendsto (fun j => realizeWeightedTopSection E g μ hμ h hh φ hφ
      (weightedTopChartSection E g μ hμ h hh φ hφ hE a (F j) (hF j)
        (hK.of_isClosed_subset (isClosed_tsupport _) (hsF j)) ((hsF j).trans hKO)))
      atTop (𝓝 (weightedTopCutoff E g μ hμ h hh φ hφ χ hχ hboundχ U)) := by
  classical
  let V := weightedTopCutoffSection E g μ hμ h hh φ hφ χ hχ hboundχ
    (weightedTopHilbertRepresentative E g μ hμ h hh φ hφ U)
  let G : ComplexVector n → ComplexVector r :=
    K.indicator (fun z => coefficients (r := r) E V.1 a z Fin.elim0)
  have hV : realizeWeightedTopSection E g μ hμ h hh φ hφ V =
      weightedTopCutoff E g μ hμ h hh φ hφ χ hχ hboundχ U := by
    rw [← weightedTopHilbertRepresentative_realize E g μ hμ h hh φ hφ U,
      weightedTopCutoff_realize]
  have hsG : tsupport G ⊆ K := by
    apply closure_minimal _ hK.isClosed
    intro z hz
    by_contra hn
    exact hz (Set.indicator_of_notMem hn _)
  have hpush : V.1 = topFormPushforward (r := r) E a G := by
    apply topForm_eq_pushforward_of_chart_coefficients E V.1 a G
    · intro x hx
      have hχz : χ x = 0 := image_eq_zero_of_notMem_tsupport (fun hs => hx (hsχ hs))
      apply Subtype.ext
      change (χ x : ℂ) • _ = 0
      rw [hχz, Complex.ofReal_zero, zero_smul]
    · intro z hz
      by_cases hzK : z ∈ K
      · simp only [G, Set.indicator_of_mem hzK]
      · have hpull : L18Aux.chartPullbackZero a χ z = 0 :=
          image_eq_zero_of_notMem_tsupport (fun hs => hzK (hKχ hs))
        have hχz : χ (chartInv a z) = 0 := by
          simpa only [L18Aux.chartPullbackZero, ite_eq_left hz.1] using hpull
        simp only [G, Set.indicator_of_notMem hzK]
        ext α
        change coefficients (r := r) E (multiplyForm E (fun x => (χ x : ℂ))
          (weightedTopHilbertRepresentative E g μ hμ h hh φ hφ U).1) a z Fin.elim0 α = 0
        rw [coefficients_multiplyForm, hχz, Complex.ofReal_zero, zero_mul]
  have hGae (α : Fin r) : (fun z => G z α) =ᵐ[lebesgueC n]
      (fun z => compactTopHilbertField E g μ hμ h hh φ hφ a K hK hKO
        (weightedTopCutoff E g μ hμ h hh φ hφ χ hχ hboundχ U) z α) := by
    have hi := compactTopHilbertField_realize_ae E g μ hμ h hh φ hφ a K hK hKO V α
    rw [hV] at hi
    apply EventuallyEq.trans _ hi.symm
    exact Eventually.of_forall fun z => by
      by_cases hz : z ∈ K
      · simp only [G, Set.indicator_of_mem hz]
      · simp only [G, Set.indicator_of_notMem hz, PiLp.zero_apply]
  have heG (j : ℕ) (α : Fin r) : MemLp (fun z => F j z α - G z α) 2 (lebesgueC n) :=
    (he j α).ae_eq ((hGae α).mono fun z hz => congrArg (fun w => F j z α - w) hz.symm)
  have htG (α : Fin r) : Tendsto
      (fun j => ∫ z, ‖F j z α - G z α‖ ^ 2 ∂lebesgueC n) atTop (𝓝 0) := by
    convert ht α using 1
    funext j
    apply integral_congr_ae
    filter_upwards [hGae α] with z hz
    rw [hz]
  have hlim := weightedTopChartSection_tendsto_of_model_arrays E g μ hμ h hh φ hφ hE
    a K hK hKO F hF hsF G hsG V hpush heG htG
  rwa [hV] at hlim

/-- The zero-extended scalar model of the cutoff gives the same compact field. -/
theorem compactTopHilbertField_cutoff_pullback_ae
    (a : M.Carrier) (K : Set (ComplexVector n)) (hK : IsCompact K)
    (hKO : K ⊆ localDomain (r := r) E a)
    (χ : M.Carrier → ℝ) (hχ : SmoothFn χ)
    (hboundχ : ∀ x, χ x ∈ Set.Icc (0 : ℝ) 1)
    (U : WeightedTopHilbert E g μ hμ h hh φ hφ) (α : Fin r) :
    (fun z => compactTopHilbertField E g μ hμ h hh φ hφ a K hK hKO
      (weightedTopCutoff E g μ hμ h hh φ hφ χ hχ hboundχ U) z α) =ᵐ[lebesgueC n]
      (fun z => Complex.ofReal (L18Aux.chartPullbackZero a χ z) *
        compactTopHilbertField E g μ hμ h hh φ hφ a K hK hKO U z α) := by
  apply (compactTopHilbertField_cutoff_ae E g μ hμ h hh φ hφ a K hK hKO χ hχ hboundχ U α).trans
  exact Eventually.of_forall fun z => by
    by_cases hz : z ∈ K
    · simp only [L18Aux.chartPullbackZero, ite_eq_left (hKO hz).1]
    · simp only [compactTopHilbertField, compactLpField, Set.indicator_of_notMem hz, mul_zero]

/-- The form used in the joint local model approximation reconstructs the
actual completed cutoff of the top-form input. -/
theorem weightedTopChartSection_tendsto_cutoff_of_pullback_model_errors
    (hE : Holomorphic (r := r) E)
    (a : M.Carrier) (K : Set (ComplexVector n)) (hK : IsCompact K)
    (hKO : K ⊆ localDomain (r := r) E a)
    (χ : M.Carrier → ℝ) (hχ : SmoothFn χ)
    (hboundχ : ∀ x, χ x ∈ Set.Icc (0 : ℝ) 1)
    (hsχ : tsupport χ ⊆ bundleChartSource (r := r) E a)
    (hKχ : tsupport (L18Aux.chartPullbackZero a χ) ⊆ K)
    (U : WeightedTopHilbert E g μ hμ h hh φ hφ)
    (F : ℕ → ComplexVector n → ComplexVector r)
    (hF : ∀ j, ContDiff ℝ ∞ (F j)) (hsF : ∀ j, tsupport (F j) ⊆ K)
    (he : ∀ j α, MemLp
      (fun z => F j z α - Complex.ofReal (L18Aux.chartPullbackZero a χ z) *
        compactTopHilbertField E g μ hμ h hh φ hφ a K hK hKO U z α) 2 (lebesgueC n))
    (ht : ∀ α, Tendsto (fun j => ∫ z,
      ‖F j z α - Complex.ofReal (L18Aux.chartPullbackZero a χ z) *
        compactTopHilbertField E g μ hμ h hh φ hφ a K hK hKO U z α‖ ^ 2 ∂lebesgueC n)
      atTop (𝓝 0)) :
    Tendsto (fun j => realizeWeightedTopSection E g μ hμ h hh φ hφ
      (weightedTopChartSection E g μ hμ h hh φ hφ hE a (F j) (hF j)
        (hK.of_isClosed_subset (isClosed_tsupport _) (hsF j)) ((hsF j).trans hKO)))
      atTop (𝓝 (weightedTopCutoff E g μ hμ h hh φ hφ χ hχ hboundχ U)) := by
  apply weightedTopChartSection_tendsto_cutoff_of_model_errors E g μ hμ h hh φ hφ hE
    a K hK hKO χ hχ hboundχ hsχ hKχ U F hF hsF
  · intro j α
    exact (he j α).ae_eq
      ((compactTopHilbertField_cutoff_pullback_ae E g μ hμ h hh φ hφ a K hK hKO χ hχ hboundχ U α).mono
        fun z hz => congrArg (fun w => F j z α - w) hz.symm)
  · intro α
    convert ht α using 1
    funext j
    apply integral_congr_ae
    filter_upwards [compactTopHilbertField_cutoff_pullback_ae E g μ hμ h hh φ hφ a K hK hKO χ hχ hboundχ U α]
      with z hz
    rw [hz]

theorem weightedTopCutoffSection_sub_val
    (χ : M.Carrier → ℝ) (hχ : SmoothFn χ) (hbound : ∀ x, χ x ∈ Set.Icc (0 : ℝ) 1)
    (U : WeightedTopSection E g μ hμ h hh φ hφ) :
    (weightedTopCutoffSection E g μ hμ h hh φ hφ χ hχ hbound U - U).1 =
      multiplyForm E (fun x => ((χ x - 1 : ℝ) : ℂ)) U.1 := by
  have he := WeightedTopSection.toForm_sub E g μ hμ h hh φ hφ
    (weightedTopCutoffSection E g μ hμ h hh φ hφ χ hχ hbound U) U
  change (weightedTopCutoffSection E g μ hμ h hh φ hφ χ hχ hbound U - U).1 =
    (weightedTopCutoffSection E g μ hμ h hh φ hφ χ hχ hbound U).1 - U.1 at he
  rw [he]
  funext x
  apply Subtype.ext
  change (χ x : ℂ) • (U.1 x).1 - (U.1 x).1 = ((χ x - 1 : ℝ) : ℂ) • (U.1 x).1
  rw [Complex.ofReal_sub, Complex.ofReal_one]
  simpa only [one_smul] using (sub_smul (χ x : ℂ) 1 (U.1 x).1).symm

theorem weightedTopCutoffSection_tendsto
    (χ : ℕ → M.Carrier → ℝ) (hχ : ∀ m, SmoothFn (χ m))
    (hbound : ∀ m x, χ m x ∈ Set.Icc (0 : ℝ) 1)
    (hpoint : ∀ x, ∀ᶠ m in atTop, χ m x = 1)
    (U : WeightedTopSection E g μ hμ h hh φ hφ) :
    Tendsto (fun m => realizeWeightedTopSection E g μ hμ h hh φ hφ
      (weightedTopCutoffSection E g μ hμ h hh φ hφ (χ m) (hχ m) (hbound m) U))
      atTop (𝓝 (realizeWeightedTopSection E g μ hμ h hh φ hφ U)) := by
  let V := fun m => weightedTopCutoffSection E g μ hμ h hh φ hφ (χ m) (hχ m) (hbound m) U
  let B := fun x => BundleDbar.formNormSq (r := r) E g.form h U.1 x * Real.exp (-φ x)
  let F := fun m x => (χ m x - 1) ^ 2 * B x
  have hB : Integrable B μ := weightedTopNorm_integrable E g μ hμ h hh φ hφ U.1 U.2
  have hnB (x : M.Carrier) : 0 ≤ B x :=
    mul_nonneg (formNormSq_top_nonneg E g.form h U.1 x) (Real.exp_pos _).le
  have hnF (m : ℕ) (x : M.Carrier) : 0 ≤ F m x := mul_nonneg (sq_nonneg _) (hnB x)
  have hFm (m : ℕ) : AEStronglyMeasurable (F m) μ :=
    (((L18Aux.continuous_of_smoothFn (hχ m)).sub continuous_const).pow 2).aestronglyMeasurable.mul hB.aestronglyMeasurable
  have hFlim : Tendsto (fun m => ∫ x, F m x ∂μ) atTop (𝓝 0) := by
    have ht := tendsto_integral_of_dominated_convergence B hFm hB
      (fun m => Eventually.of_forall fun x => by
        rw [Real.norm_of_nonneg (hnF m x)]
        have h0 := (hbound m x).1
        have h1 := (hbound m x).2
        have hs : (χ m x - 1) ^ 2 ≤ 1 := by nlinarith
        exact mul_le_of_le_one_left (hnB x) hs)
      (Eventually.of_forall fun x => by
        have he : (fun m => F m x) =ᶠ[atTop] (fun _ => 0) :=
          (hpoint x).mono (fun m hm => by simp only [F, hm, sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul])
        exact tendsto_const_nhds.congr' he.symm)
    simpa only [integral_zero] using ht
  have hsq (m : ℕ) :
      ‖realizeWeightedTopSection E g μ hμ h hh φ hφ (V m) -
        realizeWeightedTopSection E g μ hμ h hh φ hφ U‖ ^ 2 = ∫ x, F m x ∂μ := by
    rw [← realizeWeightedTopSection_sub E g μ hμ h hh φ hφ, realizeWeightedTopSection_norm_sq]
    change (weightedNormSq (r := r) E g.form h μ φ (V m - U).1).toReal = _
    rw [weightedNormSq_top_eq_ofReal_integral E g μ hμ h hh φ hφ (V m - U).1 (V m - U).2]
    have hfun (x : M.Carrier) : BundleDbar.formNormSq (r := r) E g.form h (V m - U).1 x * Real.exp (-φ x) = F m x := by
      rw [weightedTopCutoffSection_sub_val E g μ hμ h hh φ hφ (χ m) (hχ m) (hbound m) U,
        formNormSq_multiply_real_top]
      simp only [F, B]
      ring
    simp_rw [hfun]
    exact ENNReal.toReal_ofReal (integral_nonneg (hnF m))
  have hpow : Tendsto (fun m => ‖realizeWeightedTopSection E g μ hμ h hh φ hφ (V m) -
      realizeWeightedTopSection E g μ hμ h hh φ hφ U‖ ^ 2) atTop (𝓝 0) := by
    simpa only [hsq] using hFlim
  have hnorm := Real.continuous_sqrt.continuousAt.tendsto.comp hpow
  simp only [Real.sqrt_zero] at hnorm
  have hnorm' : Tendsto (fun m => ‖realizeWeightedTopSection E g μ hμ h hh φ hφ (V m) -
      realizeWeightedTopSection E g μ hμ h hh φ hφ U‖) atTop (𝓝 0) := by
    convert hnorm using 1
    funext m
    exact (Real.sqrt_sq (norm_nonneg _)).symm
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hnorm'

/-- Exhausting smooth cutoffs converge strongly on every actual completed
top form. -/
theorem weightedTopCutoff_tendsto
    (χ : ℕ → M.Carrier → ℝ) (hχ : ∀ m, SmoothFn (χ m))
    (hbound : ∀ m x, χ m x ∈ Set.Icc (0 : ℝ) 1)
    (hpoint : ∀ x, ∀ᶠ m in atTop, χ m x = 1)
    (U : WeightedTopHilbert E g μ hμ h hh φ hφ) :
    Tendsto (fun m => weightedTopCutoff E g μ hμ h hh φ hφ
      (χ m) (hχ m) (hbound m) U) atTop (𝓝 U) := by
  have ht := weightedTopCutoffSection_tendsto E g μ hμ h hh φ hφ χ hχ hbound hpoint
    (weightedTopHilbertRepresentative E g μ hμ h hh φ hφ U)
  simpa only [← weightedTopCutoff_realize, weightedTopHilbertRepresentative_realize] using ht

end Yau.LeafProofs.L14Aux
