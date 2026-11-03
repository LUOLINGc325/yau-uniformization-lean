import Yau.LeafProofs.L14TwoL2
import Yau.LeafProofs.L14CutoffNorm

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

theorem formNormSq_multiply_real_two (g : HermitianField M) (h : Metric E)
    (χ : M.Carrier → ℝ) (u : NQForm E 2) (x : M.Carrier) :
    BundleDbar.formNormSq (r := r) E g h (multiplyForm E (fun x => (χ x : ℂ)) u) x =
      χ x ^ 2 * BundleDbar.formNormSq (r := r) E g h u x := by
  have he : multiplyForm E (fun x => (χ x : ℂ)) u x = ((χ x : ℂ) • u) x := by
    apply Subtype.ext
    rfl
  rw [formNormSq_congr_at E g h _ _ x he, formNormSq_two_smul]
  simp only [Complex.normSq_ofReal, pow_two]

theorem weightedL2_multiply_real_two (g : HermitianField M) (μ : Measure M.Carrier)
    (h : Metric E) (φ : M.Carrier → ℝ) (χ : M.Carrier → ℝ) (hχ : SmoothFn χ)
    (u : NQForm E 2) (hu : WeightedL2 (r := r) E g h μ φ u)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ x, χ x ^ 2 ≤ C) :
    WeightedL2 (r := r) E g h μ φ (multiplyForm E (fun x => (χ x : ℂ)) u) := by
  have hη (a : M.Carrier) : ContinuousOn (inChart a (fun x => (χ x : ℂ))) (localDomain (r := r) E a) :=
    (((hχ a).continuousLinearMap_comp Complex.ofRealCLM).continuousOn.mono Set.inter_subset_left)
  refine ⟨locallyL2_multiplyForm E (fun x => (χ x : ℂ)) hη u hu.1, ?_⟩
  have hn (x : M.Carrier) : 0 ≤ BundleDbar.formNormSq (r := r) E g h u x * Real.exp (-φ x) :=
    mul_nonneg (formNormSq_two_nonneg E g h u x) (Real.exp_pos _).le
  have hle : weightedNormSq (r := r) E g h μ φ (multiplyForm E (fun x => (χ x : ℂ)) u) ≤
      ENNReal.ofReal C * weightedNormSq (r := r) E g h μ φ u := by
    calc
      _ ≤ ∫⁻ x, ENNReal.ofReal (C * (BundleDbar.formNormSq (r := r) E g h u x * Real.exp (-φ x))) ∂μ := by
        apply lintegral_mono
        intro x
        change ENNReal.ofReal (BundleDbar.formNormSq (r := r) E g h
          (multiplyForm E (fun x => (χ x : ℂ)) u) x * Real.exp (-φ x)) ≤ _
        rw [formNormSq_multiply_real_two]
        apply ENNReal.ofReal_le_ofReal
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hbound x) (hn x)
      _ = _ := by
        simp only [ENNReal.ofReal_mul hC]
        exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  exact hle.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hu.2)

variable (g : Yau.SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
  (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)

def weightedTwoCutoffSection (χ : M.Carrier → ℝ) (hχ : SmoothFn χ)
    (hbound : ∀ x, χ x ∈ Set.Icc (0 : ℝ) 1) (U : WeightedTwoSection E g μ hμ h hh φ hφ) :
    WeightedTwoSection E g μ hμ h hh φ hφ :=
  ⟨multiplyForm E (fun x => (χ x : ℂ)) U.1,
    weightedL2_multiply_real_two E g.form μ h φ χ hχ U.1 U.2 1 (by norm_num)
      (fun x => by have h0 := (hbound x).1; have h1 := (hbound x).2; nlinarith)⟩

/-- Multiplication by an arbitrary smooth, uniformly bounded real function. -/
def weightedTwoMultiplierSection (χ : M.Carrier → ℝ) (hχ : SmoothFn χ)
    (C : ℝ) (_hC : 0 ≤ C) (hbound : ∀ x, χ x ^ 2 ≤ C ^ 2)
    (U : WeightedTwoSection E g μ hμ h hh φ hφ) :
    WeightedTwoSection E g μ hμ h hh φ hφ :=
  ⟨multiplyForm E (fun x => (χ x : ℂ)) U.1,
    weightedL2_multiply_real_two E g.form μ h φ χ hχ U.1 U.2 (C ^ 2)
      (sq_nonneg C) hbound⟩

@[simp] theorem weightedTwoCutoffSection_toForm (χ : M.Carrier → ℝ) (hχ : SmoothFn χ)
    (hbound : ∀ x, χ x ∈ Set.Icc (0 : ℝ) 1)
    (U : WeightedTwoSection E g μ hμ h hh φ hφ) :
    (weightedTwoCutoffSection E g μ hμ h hh φ hφ χ hχ hbound U).toForm E g μ hμ h hh φ hφ =
      multiplyForm E (fun x => (χ x : ℂ)) (U.toForm E g μ hμ h hh φ hφ) := rfl

@[simp] theorem weightedTwoMultiplierSection_toForm (χ : M.Carrier → ℝ) (hχ : SmoothFn χ)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ x, χ x ^ 2 ≤ C ^ 2)
    (U : WeightedTwoSection E g μ hμ h hh φ hφ) :
    (weightedTwoMultiplierSection E g μ hμ h hh φ hφ χ hχ C hC hbound U).toForm E g μ hμ h hh φ hφ =
      multiplyForm E (fun x => (χ x : ℂ)) (U.toForm E g μ hμ h hh φ hφ) := rfl

theorem weightedTwoMultiplierSection_norm_le (χ : M.Carrier → ℝ) (hχ : SmoothFn χ)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ x, χ x ^ 2 ≤ C ^ 2)
    (U : WeightedTwoSection E g μ hμ h hh φ hφ) :
    ‖weightedTwoMultiplierSection E g μ hμ h hh φ hφ χ hχ C hC hbound U‖ ≤ C * ‖U‖ := by
  let V := weightedTwoMultiplierSection E g μ hμ h hh φ hφ χ hχ C hC hbound U
  have hle : weightedNormSq (r := r) E g.form h μ φ V.1 ≤
      ENNReal.ofReal (C ^ 2) * weightedNormSq (r := r) E g.form h μ φ U.1 := by
    calc
      _ ≤ ∫⁻ x, ENNReal.ofReal (C ^ 2 *
          (BundleDbar.formNormSq (r := r) E g.form h U.1 x * Real.exp (-φ x))) ∂μ := by
        apply lintegral_mono
        intro x
        change ENNReal.ofReal (BundleDbar.formNormSq (r := r) E g.form h
          (multiplyForm E (fun x => (χ x : ℂ)) U.1) x * Real.exp (-φ x)) ≤ _
        rw [formNormSq_multiply_real_two]
        apply ENNReal.ofReal_le_ofReal
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hbound x)
          (mul_nonneg (formNormSq_two_nonneg E g.form h U.1 x) (Real.exp_pos _).le)
      _ = _ := by
        simp only [ENNReal.ofReal_mul (sq_nonneg C)]
        exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have hreal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top U.2.2.ne) hle
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg C)] at hreal
  have hV := weightedTwoSection_norm_sq E g μ hμ h hh φ hφ V
  have hU := weightedTwoSection_norm_sq E g μ hμ h hh φ hφ U
  change ‖V‖ ^ 2 = (weightedNormSq (r := r) E g.form h μ φ V.1).toReal at hV
  change ‖U‖ ^ 2 = (weightedNormSq (r := r) E g.form h μ φ U.1).toReal at hU
  rw [← hV, ← hU] at hreal
  change ‖V‖ ≤ C * ‖U‖
  nlinarith [norm_nonneg V, norm_nonneg U, mul_nonneg hC (norm_nonneg U)]

def weightedTwoMultiplierLinearMap (χ : M.Carrier → ℝ) (hχ : SmoothFn χ)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ x, χ x ^ 2 ≤ C ^ 2) :
    WeightedTwoSection E g μ hμ h hh φ hφ →ₗ[ℂ]
      WeightedTwoSection E g μ hμ h hh φ hφ where
  toFun := weightedTwoMultiplierSection E g μ hμ h hh φ hφ χ hχ C hC hbound
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

def weightedTwoMultiplierRaw (χ : M.Carrier → ℝ) (hχ : SmoothFn χ)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ x, χ x ^ 2 ≤ C ^ 2) :
    WeightedTwoSection E g μ hμ h hh φ hφ →L[ℂ]
      WeightedTwoSection E g μ hμ h hh φ hφ :=
  (weightedTwoMultiplierLinearMap E g μ hμ h hh φ hφ χ hχ C hC hbound).mkContinuous C
    (weightedTwoMultiplierSection_norm_le E g μ hμ h hh φ hφ χ hχ C hC hbound)

/-- The actual bounded multiplier on the separated completion of weighted two-forms. -/
def weightedTwoMultiplier (χ : M.Carrier → ℝ) (hχ : SmoothFn χ)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ x, χ x ^ 2 ≤ C ^ 2) :
    WeightedTwoHilbert E g μ hμ h hh φ hφ →L[ℂ]
      WeightedTwoHilbert E g μ hμ h hh φ hφ :=
  (weightedTwoMultiplierRaw E g μ hμ h hh φ hφ χ hχ C hC hbound).completion

theorem weightedTwoMultiplier_realize (χ : M.Carrier → ℝ) (hχ : SmoothFn χ)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ x, χ x ^ 2 ≤ C ^ 2)
    (U : WeightedTwoSection E g μ hμ h hh φ hφ) :
    weightedTwoMultiplier E g μ hμ h hh φ hφ χ hχ C hC hbound
      (realizeWeightedTwoSection E g μ hμ h hh φ hφ U) =
      realizeWeightedTwoSection E g μ hμ h hh φ hφ
        (weightedTwoMultiplierSection E g μ hμ h hh φ hφ χ hχ C hC hbound U) :=
  ContinuousLinearMap.completion_apply_coe _ U

theorem weightedTwoMultiplier_norm_le (χ : M.Carrier → ℝ) (hχ : SmoothFn χ)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ x, χ x ^ 2 ≤ C ^ 2)
    (W : WeightedTwoHilbert E g μ hμ h hh φ hφ) :
    ‖weightedTwoMultiplier E g μ hμ h hh φ hφ χ hχ C hC hbound W‖ ≤ C * ‖W‖ := by
  induction W using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_le (by fun_prop) (by fun_prop)
  | ih U =>
    change ‖weightedTwoMultiplier E g μ hμ h hh φ hφ χ hχ C hC hbound
      (realizeWeightedTwoSection E g μ hμ h hh φ hφ U)‖ ≤
      C * ‖realizeWeightedTwoSection E g μ hμ h hh φ hφ U‖
    rw [weightedTwoMultiplier_realize E g μ hμ h hh φ hφ]
    simpa only [realizeWeightedTwoSection, UniformSpace.Completion.norm_coe] using
      weightedTwoMultiplierSection_norm_le E g μ hμ h hh φ hφ χ hχ C hC hbound U

theorem weightedTwoMultiplier_opNorm_le (χ : M.Carrier → ℝ) (hχ : SmoothFn χ)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ x, χ x ^ 2 ≤ C ^ 2) :
    ‖weightedTwoMultiplier E g μ hμ h hh φ hφ χ hχ C hC hbound‖ ≤ C :=
  ContinuousLinearMap.opNorm_le_bound _ hC
    (weightedTwoMultiplier_norm_le E g μ hμ h hh φ hφ χ hχ C hC hbound)

/-- A cutoff multiplier is a contraction on the actual Hilbert completion. -/
def weightedTwoCutoff (χ : M.Carrier → ℝ) (hχ : SmoothFn χ)
    (hbound : ∀ x, χ x ∈ Set.Icc (0 : ℝ) 1) :
    WeightedTwoHilbert E g μ hμ h hh φ hφ →L[ℂ]
      WeightedTwoHilbert E g μ hμ h hh φ hφ :=
  weightedTwoMultiplier E g μ hμ h hh φ hφ χ hχ 1 zero_le_one
    (fun x => by have h0 := (hbound x).1; have h1 := (hbound x).2; nlinarith)

theorem weightedTwoCutoff_realize (χ : M.Carrier → ℝ) (hχ : SmoothFn χ)
    (hbound : ∀ x, χ x ∈ Set.Icc (0 : ℝ) 1)
    (U : WeightedTwoSection E g μ hμ h hh φ hφ) :
    weightedTwoCutoff E g μ hμ h hh φ hφ χ hχ hbound
      (realizeWeightedTwoSection E g μ hμ h hh φ hφ U) =
      realizeWeightedTwoSection E g μ hμ h hh φ hφ
        (weightedTwoCutoffSection E g μ hμ h hh φ hφ χ hχ hbound U) := by
  exact ContinuousLinearMap.completion_apply_coe _ U

theorem weightedTwoCutoff_norm_le (χ : M.Carrier → ℝ) (hχ : SmoothFn χ)
    (hbound : ∀ x, χ x ∈ Set.Icc (0 : ℝ) 1)
    (W : WeightedTwoHilbert E g μ hμ h hh φ hφ) :
    ‖weightedTwoCutoff E g μ hμ h hh φ hφ χ hχ hbound W‖ ≤ ‖W‖ := by
  exact (one_mul ‖W‖) ▸ weightedTwoMultiplier_norm_le E g μ hμ h hh φ hφ χ hχ 1 zero_le_one _ W

theorem weightedTwoCutoff_opNorm_le (χ : M.Carrier → ℝ) (hχ : SmoothFn χ)
    (hbound : ∀ x, χ x ∈ Set.Icc (0 : ℝ) 1) :
    ‖weightedTwoCutoff E g μ hμ h hh φ hφ χ hχ hbound‖ ≤ 1 :=
  weightedTwoMultiplier_opNorm_le E g μ hμ h hh φ hφ χ hχ 1 zero_le_one _

theorem realizeWeightedTwoSection_sub
    (V U : WeightedTwoSection E g μ hμ h hh φ hφ) :
    realizeWeightedTwoSection E g μ hμ h hh φ hφ (V - U) =
      realizeWeightedTwoSection E g μ hμ h hh φ hφ V - realizeWeightedTwoSection E g μ hμ h hh φ hφ U :=
  map_sub (UniformSpace.Completion.toCompl : WeightedTwoSection E g μ hμ h hh φ hφ →+
    WeightedTwoHilbert E g μ hμ h hh φ hφ) V U

theorem weightedTwoCutoffSection_sub_val
    (χ : M.Carrier → ℝ) (hχ : SmoothFn χ) (hbound : ∀ x, χ x ∈ Set.Icc (0 : ℝ) 1)
    (U : WeightedTwoSection E g μ hμ h hh φ hφ) :
    (weightedTwoCutoffSection E g μ hμ h hh φ hφ χ hχ hbound U - U).1 =
      multiplyForm E (fun x => ((χ x - 1 : ℝ) : ℂ)) U.1 := by
  have he := WeightedTwoSection.toForm_sub E g μ hμ h hh φ hφ
    (weightedTwoCutoffSection E g μ hμ h hh φ hφ χ hχ hbound U) U
  change (weightedTwoCutoffSection E g μ hμ h hh φ hφ χ hχ hbound U - U).1 =
    (weightedTwoCutoffSection E g μ hμ h hh φ hφ χ hχ hbound U).1 - U.1 at he
  rw [he]
  funext x
  apply Subtype.ext
  change (χ x : ℂ) • (U.1 x).1 - (U.1 x).1 = ((χ x - 1 : ℝ) : ℂ) • (U.1 x).1
  rw [Complex.ofReal_sub, Complex.ofReal_one]
  simpa only [one_smul] using (sub_smul (χ x : ℂ) 1 (U.1 x).1).symm

theorem weightedTwoCutoffSection_tendsto
    (χ : ℕ → M.Carrier → ℝ) (hχ : ∀ m, SmoothFn (χ m))
    (hbound : ∀ m x, χ m x ∈ Set.Icc (0 : ℝ) 1)
    (hpoint : ∀ x, ∀ᶠ m in atTop, χ m x = 1)
    (U : WeightedTwoSection E g μ hμ h hh φ hφ) :
    Tendsto (fun m => realizeWeightedTwoSection E g μ hμ h hh φ hφ
      (weightedTwoCutoffSection E g μ hμ h hh φ hφ (χ m) (hχ m) (hbound m) U))
      atTop (𝓝 (realizeWeightedTwoSection E g μ hμ h hh φ hφ U)) := by
  let V := fun m => weightedTwoCutoffSection E g μ hμ h hh φ hφ (χ m) (hχ m) (hbound m) U
  let B := fun x => BundleDbar.formNormSq (r := r) E g.form h U.1 x * Real.exp (-φ x)
  let F := fun m x => (χ m x - 1) ^ 2 * B x
  have hB : Integrable B μ := weightedTwoNorm_integrable E g μ hμ h hh φ hφ U.1 U.2
  have hnB (x : M.Carrier) : 0 ≤ B x :=
    mul_nonneg (formNormSq_two_nonneg E g.form h U.1 x) (Real.exp_pos _).le
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
      ‖realizeWeightedTwoSection E g μ hμ h hh φ hφ (V m) -
        realizeWeightedTwoSection E g μ hμ h hh φ hφ U‖ ^ 2 = ∫ x, F m x ∂μ := by
    rw [← realizeWeightedTwoSection_sub E g μ hμ h hh φ hφ, realizeWeightedTwoSection_norm_sq]
    change (weightedNormSq (r := r) E g.form h μ φ (V m - U).1).toReal = _
    rw [weightedNormSq_two_eq_ofReal_integral E g μ hμ h hh φ hφ (V m - U).1 (V m - U).2]
    have hfun (x : M.Carrier) : BundleDbar.formNormSq (r := r) E g.form h (V m - U).1 x * Real.exp (-φ x) = F m x := by
      rw [weightedTwoCutoffSection_sub_val E g μ hμ h hh φ hφ (χ m) (hχ m) (hbound m) U,
        formNormSq_multiply_real_two]
      simp only [F, B]
      ring
    simp_rw [hfun]
    exact ENNReal.toReal_ofReal (integral_nonneg (hnF m))
  have hpow : Tendsto (fun m => ‖realizeWeightedTwoSection E g μ hμ h hh φ hφ (V m) -
      realizeWeightedTwoSection E g μ hμ h hh φ hφ U‖ ^ 2) atTop (𝓝 0) := by
    simpa only [hsq] using hFlim
  have hnorm := Real.continuous_sqrt.continuousAt.tendsto.comp hpow
  simp only [Real.sqrt_zero] at hnorm
  have hnorm' : Tendsto (fun m => ‖realizeWeightedTwoSection E g μ hμ h hh φ hφ (V m) -
      realizeWeightedTwoSection E g μ hμ h hh φ hφ U‖) atTop (𝓝 0) := by
    convert hnorm using 1
    funext m
    exact (Real.sqrt_sq (norm_nonneg _)).symm
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hnorm'

/-- Cutoffs converge strongly on every point of the actual weighted two-form completion. -/
theorem weightedTwoCutoff_tendsto
    (χ : ℕ → M.Carrier → ℝ) (hχ : ∀ m, SmoothFn (χ m))
    (hbound : ∀ m x, χ m x ∈ Set.Icc (0 : ℝ) 1)
    (hpoint : ∀ x, ∀ᶠ m in atTop, χ m x = 1)
    (W : WeightedTwoHilbert E g μ hμ h hh φ hφ) :
    Tendsto (fun m => weightedTwoCutoff E g μ hμ h hh φ hφ
      (χ m) (hχ m) (hbound m) W) atTop (𝓝 W) := by
  let T := fun m => weightedTwoCutoff E g μ hμ h hh φ hφ (χ m) (hχ m) (hbound m)
  have hraw (U : WeightedTwoSection E g μ hμ h hh φ hφ) :
      Tendsto (fun m => T m (realizeWeightedTwoSection E g μ hμ h hh φ hφ U))
        atTop (𝓝 (realizeWeightedTwoSection E g μ hμ h hh φ hφ U)) := by
    simpa only [T, weightedTwoCutoff_realize E g μ hμ h hh φ hφ] using
      weightedTwoCutoffSection_tendsto E g μ hμ h hh φ hφ χ hχ hbound hpoint U
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨U, hU⟩ := (realizeWeightedTwoSection_denseRange E g μ hμ h hh φ hφ).exists_dist_lt W
    (show 0 < ε / 4 by positivity)
  let V := realizeWeightedTwoSection E g μ hμ h hh φ hφ U
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (hraw U) (ε / 2) (by positivity)
  refine ⟨N, fun m hm => ?_⟩
  have hmul : dist (T m W) (T m V) ≤ dist W V := by
    rw [dist_eq_norm, ← map_sub, dist_eq_norm]
    exact weightedTwoCutoff_norm_le E g μ hμ h hh φ hφ (χ m) (hχ m) (hbound m) (W - V)
  calc
    dist (T m W) W ≤ dist (T m W) (T m V) + dist (T m V) W := dist_triangle _ _ _
    _ ≤ dist W V + (dist (T m V) V + dist V W) :=
      add_le_add hmul (dist_triangle _ _ _)
    _ < ε := by
      have hNV : dist (T m V) V < ε / 2 := hN m hm
      change dist W V < ε / 4 at hU
      rw [dist_comm V W]
      linarith

end Yau.LeafProofs.L14Aux
