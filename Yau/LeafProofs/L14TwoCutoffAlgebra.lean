import Yau.LeafProofs.L14TwoCutoff
import Yau.LeafProofs.L14TwoMultipliers

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder ENNReal
open MeasureTheory Bundle Filter Module
namespace Yau.LeafProofs.L14Aux
open BundleDbar

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)] [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

theorem multiplyForm_real_mul {q : ℕ} (χ η : M.Carrier → ℝ) (u : NQForm E q) :
    multiplyForm E (fun x => (χ x : ℂ)) (multiplyForm E (fun x => (η x : ℂ)) u) =
      multiplyForm E (fun x => ((χ x * η x : ℝ) : ℂ)) u := by
  funext x
  apply Subtype.ext
  change (χ x : ℂ) • ((η x : ℂ) • (u x).1) = ((χ x * η x : ℝ) : ℂ) • (u x).1
  rw [Complex.ofReal_mul, mul_smul]

theorem cutoff_mul_mem_Icc (χ η : M.Carrier → ℝ)
    (hχ : ∀ x, χ x ∈ Set.Icc (0 : ℝ) 1) (hη : ∀ x, η x ∈ Set.Icc (0 : ℝ) 1) :
    ∀ x, χ x * η x ∈ Set.Icc (0 : ℝ) 1 := by
  intro x
  exact ⟨mul_nonneg (hχ x).1 (hη x).1, (mul_le_mul_of_nonneg_right (hχ x).2 (hη x).1).trans (by simpa using (hη x).2)⟩

theorem cutoff_sq_mem_Icc (χ : M.Carrier → ℝ)
    (hχ : ∀ x, χ x ∈ Set.Icc (0 : ℝ) 1) : ∀ x, χ x ^ 2 ∈ Set.Icc (0 : ℝ) 1 := by
  simpa only [pow_two] using cutoff_mul_mem_Icc χ χ hχ hχ

theorem twoFormPairing_multiply_real (g : HermitianField M) (h : Metric E)
    (χ : M.Carrier → ℝ) (u v : NQForm E 2) (x : M.Carrier) :
    twoFormPairing E g h (multiplyForm E (fun x => (χ x : ℂ)) u) v x =
      twoFormPairing E g h u (multiplyForm E (fun x => (χ x : ℂ)) v) x := by
  change twoTensorFramePairing (g x) (h x) _ _ ((χ x : ℂ) • (u x).1) (v x).1 =
    twoTensorFramePairing (g x) (h x) _ _ (u x).1 ((χ x : ℂ) • (v x).1)
  rw [twoTensorFramePairing_smul_left, twoTensorFramePairing_smul_right]
  simp

include r in
theorem twoGradientContraction_multiply_real (g : HermitianField M)
    (χ : M.Carrier → ℝ) (hχ : SmoothFn χ) (η : M.Carrier → ℝ) (W : NQForm E 2) :
    twoGradientContraction E g χ (multiplyForm E (fun x => (η x : ℂ)) W) =
      multiplyForm E (fun x => (η x : ℂ)) (twoGradientContraction E g χ W) := by
  apply oneForm_ext_of_coefficients (r := r) E
  intro a z hz j α
  rw [coefficients_twoGradientContraction_apply E g χ hχ _ a z hz,
    coefficients_multiplyForm, coefficients_twoGradientContraction_apply E g χ hχ _ a z hz]
  simp_rw [coefficients_multiplyForm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  ring

variable (g : Yau.SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
  (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)

theorem weightedOneCutoffSection_norm_le (χ : M.Carrier → ℝ) (hχ : SmoothFn χ)
    (hbound : ∀ x, χ x ∈ Set.Icc (0 : ℝ) 1)
    (U : WeightedOneSection E g μ hμ h hh φ hφ) :
    ‖weightedOneCutoffSection E g μ hμ h hh φ hφ χ hχ hbound U‖ ≤ ‖U‖ := by
  let V := weightedOneCutoffSection E g μ hμ h hh φ hφ χ hχ hbound U
  have hle : weightedNormSq (r := r) E g.form h μ φ V.1 ≤ weightedNormSq (r := r) E g.form h μ φ U.1 := by
    apply lintegral_mono
    intro x
    apply ENNReal.ofReal_le_ofReal
    change BundleDbar.formNormSq (r := r) E g.form h (multiplyForm E (fun x => (χ x : ℂ)) U.1) x *
      Real.exp (-φ x) ≤ BundleDbar.formNormSq (r := r) E g.form h U.1 x * Real.exp (-φ x)
    rw [formNormSq_multiply_real_one]
    have hs : χ x ^ 2 ≤ 1 := by have h0 := (hbound x).1; have h1 := (hbound x).2; nlinarith
    have hn := mul_nonneg (formNormSq_one_nonneg (r := r) E g.form h U.1 x) (Real.exp_pos (-φ x)).le
    nlinarith [mul_le_mul_of_nonneg_right hs hn]
  have ht := ENNReal.toReal_mono U.2.2.ne hle
  have hV := weightedOneSection_norm_sq E g μ hμ h hh φ hφ V
  have hU := weightedOneSection_norm_sq E g μ hμ h hh φ hφ U
  change ‖V‖ ^ 2 = (weightedNormSq (r := r) E g.form h μ φ V.1).toReal at hV
  change ‖U‖ ^ 2 = (weightedNormSq (r := r) E g.form h μ φ U.1).toReal at hU
  rw [← hV, ← hU] at ht
  change ‖V‖ ≤ ‖U‖
  exact (sq_le_sq₀ (norm_nonneg V) (norm_nonneg U)).mp ht

def weightedOneCutoffLinearMap (χ : M.Carrier → ℝ) (hχ : SmoothFn χ)
    (hbound : ∀ x, χ x ∈ Set.Icc (0 : ℝ) 1) :
    WeightedOneSection E g μ hμ h hh φ hφ →ₗ[ℂ] WeightedOneSection E g μ hμ h hh φ hφ where
  toFun := weightedOneCutoffSection E g μ hμ h hh φ hφ χ hχ hbound
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

def weightedOneCutoffRaw (χ : M.Carrier → ℝ) (hχ : SmoothFn χ)
    (hbound : ∀ x, χ x ∈ Set.Icc (0 : ℝ) 1) :
    WeightedOneSection E g μ hμ h hh φ hφ →L[ℂ] WeightedOneSection E g μ hμ h hh φ hφ :=
  (weightedOneCutoffLinearMap E g μ hμ h hh φ hφ χ hχ hbound).mkContinuous 1
    (fun U => by
      change ‖weightedOneCutoffSection E g μ hμ h hh φ hφ χ hχ hbound U‖ ≤ 1 * ‖U‖
      simpa only [one_mul] using weightedOneCutoffSection_norm_le E g μ hμ h hh φ hφ χ hχ hbound U)

/-- Actual scalar multiplication on the completed weighted one-form space. -/
def weightedOneCutoff (χ : M.Carrier → ℝ) (hχ : SmoothFn χ)
    (hbound : ∀ x, χ x ∈ Set.Icc (0 : ℝ) 1) :
    WeightedOneHilbert E g μ hμ h hh φ hφ →L[ℂ] WeightedOneHilbert E g μ hμ h hh φ hφ :=
  (weightedOneCutoffRaw E g μ hμ h hh φ hφ χ hχ hbound).completion

theorem weightedOneCutoff_realize (χ : M.Carrier → ℝ) (hχ : SmoothFn χ)
    (hbound : ∀ x, χ x ∈ Set.Icc (0 : ℝ) 1)
    (U : WeightedOneSection E g μ hμ h hh φ hφ) :
    weightedOneCutoff E g μ hμ h hh φ hφ χ hχ hbound
      (realizeWeightedOneSection E g μ hμ h hh φ hφ U) =
      realizeWeightedOneSection E g μ hμ h hh φ hφ
        (weightedOneCutoffSection E g μ hμ h hh φ hφ χ hχ hbound U) :=
  ContinuousLinearMap.completion_apply_coe _ U

theorem weightedOneCutoff_norm_le (χ : M.Carrier → ℝ) (hχ : SmoothFn χ)
    (hbound : ∀ x, χ x ∈ Set.Icc (0 : ℝ) 1)
    (W : WeightedOneHilbert E g μ hμ h hh φ hφ) :
    ‖weightedOneCutoff E g μ hμ h hh φ hφ χ hχ hbound W‖ ≤ ‖W‖ := by
  induction W using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_le (by fun_prop) (by fun_prop)
  | ih U =>
    change ‖weightedOneCutoff E g μ hμ h hh φ hφ χ hχ hbound
      (realizeWeightedOneSection E g μ hμ h hh φ hφ U)‖ ≤ ‖realizeWeightedOneSection E g μ hμ h hh φ hφ U‖
    rw [weightedOneCutoff_realize]
    simpa only [realizeWeightedOneSection, UniformSpace.Completion.norm_coe] using
      weightedOneCutoffSection_norm_le E g μ hμ h hh φ hφ χ hχ hbound U

theorem weightedOneCutoff_opNorm_le (χ : M.Carrier → ℝ) (hχ : SmoothFn χ)
    (hbound : ∀ x, χ x ∈ Set.Icc (0 : ℝ) 1) :
    ‖weightedOneCutoff E g μ hμ h hh φ hφ χ hχ hbound‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    (fun W => by simpa using weightedOneCutoff_norm_le E g μ hμ h hh φ hφ χ hχ hbound W)

theorem weightedTwoMultiplier_inner (χ : M.Carrier → ℝ) (hχ : SmoothFn χ)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ x, χ x ^ 2 ≤ C ^ 2)
    (W V : WeightedTwoHilbert E g μ hμ h hh φ hφ) :
    inner ℂ (weightedTwoMultiplier E g μ hμ h hh φ hφ χ hχ C hC hbound W) V =
      inner ℂ W (weightedTwoMultiplier E g μ hμ h hh φ hφ χ hχ C hC hbound V) := by
  induction W using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih U =>
    induction V using UniformSpace.Completion.induction_on with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih Z =>
      change inner ℂ (weightedTwoMultiplier E g μ hμ h hh φ hφ χ hχ C hC hbound
        (realizeWeightedTwoSection E g μ hμ h hh φ hφ U))
        (realizeWeightedTwoSection E g μ hμ h hh φ hφ Z) =
        inner ℂ (realizeWeightedTwoSection E g μ hμ h hh φ hφ U)
          (weightedTwoMultiplier E g μ hμ h hh φ hφ χ hχ C hC hbound
            (realizeWeightedTwoSection E g μ hμ h hh φ hφ Z))
      rw [weightedTwoMultiplier_realize, weightedTwoMultiplier_realize,
        realizeWeightedTwoSection_inner, realizeWeightedTwoSection_inner]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => congrArg (fun c : ℂ => c * (Real.exp (-φ x) : ℂ))
        (twoFormPairing_multiply_real E g.form h χ U.1 Z.1 x)

theorem weightedTwoCutoff_inner (χ : M.Carrier → ℝ) (hχ : SmoothFn χ)
    (hbound : ∀ x, χ x ∈ Set.Icc (0 : ℝ) 1)
    (W V : WeightedTwoHilbert E g μ hμ h hh φ hφ) :
    inner ℂ (weightedTwoCutoff E g μ hμ h hh φ hφ χ hχ hbound W) V =
      inner ℂ W (weightedTwoCutoff E g μ hμ h hh φ hφ χ hχ hbound V) :=
  weightedTwoMultiplier_inner E g μ hμ h hh φ hφ χ hχ 1 zero_le_one _ W V

theorem weightedTwoCutoff_mul (χ η : M.Carrier → ℝ) (hχ : SmoothFn χ) (hη : SmoothFn η)
    (hχb : ∀ x, χ x ∈ Set.Icc (0 : ℝ) 1) (hηb : ∀ x, η x ∈ Set.Icc (0 : ℝ) 1)
    (W : WeightedTwoHilbert E g μ hμ h hh φ hφ) :
    weightedTwoCutoff E g μ hμ h hh φ hφ χ hχ hχb
      (weightedTwoCutoff E g μ hμ h hh φ hφ η hη hηb W) =
      weightedTwoCutoff E g μ hμ h hh φ hφ (fun x => χ x * η x)
        (fun a => (hχ a).mul (hη a)) (cutoff_mul_mem_Icc χ η hχb hηb) W := by
  induction W using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih U =>
    change weightedTwoCutoff E g μ hμ h hh φ hφ χ hχ hχb
      (weightedTwoCutoff E g μ hμ h hh φ hφ η hη hηb
        (realizeWeightedTwoSection E g μ hμ h hh φ hφ U)) =
      weightedTwoCutoff E g μ hμ h hh φ hφ (fun x => χ x * η x)
        (fun a => (hχ a).mul (hη a)) (cutoff_mul_mem_Icc χ η hχb hηb)
        (realizeWeightedTwoSection E g μ hμ h hh φ hφ U)
    rw [weightedTwoCutoff_realize, weightedTwoCutoff_realize, weightedTwoCutoff_realize]
    congr 1
    apply Subtype.ext
    exact multiplyForm_real_mul E χ η U.1

theorem weightedTwoCutoff_sq (χ : M.Carrier → ℝ) (hχ : SmoothFn χ)
    (hχb : ∀ x, χ x ∈ Set.Icc (0 : ℝ) 1)
    (W : WeightedTwoHilbert E g μ hμ h hh φ hφ) :
    weightedTwoCutoff E g μ hμ h hh φ hφ χ hχ hχb
      (weightedTwoCutoff E g μ hμ h hh φ hφ χ hχ hχb W) =
      weightedTwoCutoff E g μ hμ h hh φ hφ (fun x => χ x ^ 2)
        (fun a => (hχ a).pow 2) (cutoff_sq_mem_Icc χ hχb) W := by
  simpa only [pow_two] using weightedTwoCutoff_mul E g μ hμ h hh φ hφ χ χ hχ hχ hχb hχb W

theorem weightedTwoHilbertGradientContraction_cutoff
    (χ η : M.Carrier → ℝ) (hχ : SmoothFn χ) (hη : SmoothFn η)
    (hηb : ∀ x, η x ∈ Set.Icc (0 : ℝ) 1) (C : ℝ) (hC : 0 ≤ C)
    (hgrad : ∀ x, gradNormSq g.form χ x ≤ C)
    (W : WeightedTwoHilbert E g μ hμ h hh φ hφ) :
    weightedTwoHilbertGradientContraction E g μ hμ h hh φ hφ χ hχ C hC hgrad
      (weightedTwoCutoff E g μ hμ h hh φ hφ η hη hηb W) =
      weightedOneCutoff E g μ hμ h hh φ hφ η hη hηb
        (weightedTwoHilbertGradientContraction E g μ hμ h hh φ hφ χ hχ C hC hgrad W) := by
  induction W using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih U =>
    change weightedTwoHilbertGradientContraction E g μ hμ h hh φ hφ χ hχ C hC hgrad
      (weightedTwoCutoff E g μ hμ h hh φ hφ η hη hηb
        (realizeWeightedTwoSection E g μ hμ h hh φ hφ U)) =
      weightedOneCutoff E g μ hμ h hh φ hφ η hη hηb
        (weightedTwoHilbertGradientContraction E g μ hμ h hh φ hφ χ hχ C hC hgrad
          (realizeWeightedTwoSection E g μ hμ h hh φ hφ U))
    rw [weightedTwoCutoff_realize, weightedTwoHilbertGradientContraction_realize,
      weightedTwoHilbertGradientContraction_realize, weightedOneCutoff_realize]
    congr 1
    apply Subtype.ext
    exact twoGradientContraction_multiply_real (r := r) E g.form χ hχ η U.1

/-- The actual chart derivative of the square of a real smooth cutoff. -/
theorem wirtBar_cutoff_sq (χ : M.Carrier → ℝ) (hχ : SmoothFn χ)
    (a : M.Carrier) (z v : ComplexVector n) (hz : z ∈ chartTarget a) :
    wirtBar (fun w => Complex.ofReal (inChart a (fun x => χ x ^ 2) w)) z v =
      (2 * (χ (chartInv a z) : ℂ)) *
        wirtBar (fun w => Complex.ofReal (inChart a χ w)) z v := by
  have hd : DifferentiableAt ℝ (fun w => Complex.ofReal (inChart a χ w)) z :=
    (((hχ a).continuousLinearMap_comp Complex.ofRealCLM).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) a).mem_nhds hz)).differentiableAt (by simp)
  have he : (fun w => Complex.ofReal (inChart a (fun x => χ x ^ 2) w)) =
      (fun w => Complex.ofReal (inChart a χ w) * Complex.ofReal (inChart a χ w)) := by
    funext w
    simp only [inChart, pow_two, Complex.ofReal_mul]
  rw [he, wirtBar_mul_rule _ _ z v hd hd]
  change _ = 2 * Complex.ofReal (inChart a χ z) * _
  ring

/-- The square-cutoff gradient bound is derived from the true derivative. -/
theorem gradNormSq_cutoff_sq (g : HermitianField M) (χ : M.Carrier → ℝ)
    (hχ : SmoothFn χ) (x : M.Carrier) :
    gradNormSq g (fun x => χ x ^ 2) x = 4 * χ x ^ 2 * gradNormSq g χ x := by
  let v := fun i => wirtBar (fun w => Complex.ofReal (inChart x χ w)) (chartPt x x) (stdVec i)
  let G := (hMat g x (chartPt x x))⁻¹
  have hv : (fun i => wirtBar (fun w => Complex.ofReal (inChart x (fun x => χ x ^ 2) w))
      (chartPt x x) (stdVec i)) = fun i => (2 * (χ x : ℂ)) * v i := by
    funext i
    rw [wirtBar_cutoff_sq χ hχ x (chartPt x x) (stdVec i) (mem_extChartAt_target x)]
    rw [chartInv_chartPt_of_mem x x (mem_chart_source _ _)]
  rw [gradNormSq_eq_chart_bar_norm, hv, gradNormSq_eq_chart_bar_norm]
  change (star (fun i => (2 * (χ x : ℂ)) * v i) ⬝ᵥ G *ᵥ
      (fun i => (2 * (χ x : ℂ)) * v i)).re = 4 * χ x ^ 2 * (star v ⬝ᵥ G *ᵥ v).re
  have he : star (fun i => (2 * (χ x : ℂ)) * v i) ⬝ᵥ G *ᵥ
      (fun i => (2 * (χ x : ℂ)) * v i) =
      ((4 * χ x ^ 2 : ℝ) : ℂ) * (star v ⬝ᵥ G *ᵥ v) := by
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_mul, star_ofNat, Complex.star_def,
      Complex.conj_ofReal, Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_pow, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he]
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem gradNormSq_cutoff_sq_le (g : HermitianField M) (χ : M.Carrier → ℝ)
    (hχ : SmoothFn χ) (hχb : ∀ x, χ x ∈ Set.Icc (0 : ℝ) 1)
    (C : ℝ) (hC : 0 ≤ C) (hgrad : ∀ x, gradNormSq g χ x ≤ C) :
    ∀ x, gradNormSq g (fun x => χ x ^ 2) x ≤ 4 * C := by
  intro x
  rw [gradNormSq_cutoff_sq g χ hχ]
  calc
    _ ≤ 4 * χ x ^ 2 * C := mul_le_mul_of_nonneg_left (hgrad x) (by positivity)
    _ ≤ 4 * C := by
      have hb := (cutoff_sq_mem_Icc χ hχb x).2
      nlinarith [mul_le_mul_of_nonneg_right hb hC]

include r in
theorem twoGradientContraction_cutoff_sq (g : HermitianField M)
    (χ : M.Carrier → ℝ) (hχ : SmoothFn χ) (W : NQForm E 2) :
    twoGradientContraction E g (fun x => χ x ^ 2) W =
      (2 : ℂ) • multiplyForm E (fun x => (χ x : ℂ)) (twoGradientContraction E g χ W) := by
  apply oneForm_ext_of_coefficients (r := r) E
  intro a z hz j α
  rw [coefficients_twoGradientContraction_apply E g (fun x => χ x ^ 2) (fun a => (hχ a).pow 2) _ a z hz,
    coefficients_smul, coefficients_multiplyForm, coefficients_twoGradientContraction_apply E g χ hχ _ a z hz]
  simp_rw [wirtBar_cutoff_sq χ hχ a z _ hz.1]
  simp only [star_mul, star_ofNat, Complex.star_def, Complex.conj_ofReal]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- The true contraction for `χ²`, with its derived `4C` bound, on every Hilbert point. -/
theorem weightedTwoHilbertGradientContraction_cutoff_sq
    (χ : M.Carrier → ℝ) (hχ : SmoothFn χ) (hχb : ∀ x, χ x ∈ Set.Icc (0 : ℝ) 1)
    (C : ℝ) (hC : 0 ≤ C) (hgrad : ∀ x, gradNormSq g.form χ x ≤ C)
    (W : WeightedTwoHilbert E g μ hμ h hh φ hφ) :
    weightedTwoHilbertGradientContraction E g μ hμ h hh φ hφ (fun x => χ x ^ 2)
      (fun a => (hχ a).pow 2) (4 * C) (by positivity)
      (gradNormSq_cutoff_sq_le g.form χ hχ hχb C hC hgrad) W =
      (2 : ℂ) • weightedOneCutoff E g μ hμ h hh φ hφ χ hχ hχb
        (weightedTwoHilbertGradientContraction E g μ hμ h hh φ hφ χ hχ C hC hgrad W) := by
  refine UniformSpace.Completion.induction_on W ?_ ?_
  · exact isClosed_eq
      (weightedTwoHilbertGradientContraction E g μ hμ h hh φ hφ (fun x => χ x ^ 2)
        (fun a => (hχ a).pow 2) (4 * C) (by positivity)
        (gradNormSq_cutoff_sq_le g.form χ hχ hχb C hC hgrad)).continuous
      (((weightedOneCutoff E g μ hμ h hh φ hφ χ hχ hχb).continuous.comp
        (weightedTwoHilbertGradientContraction E g μ hμ h hh φ hφ χ hχ C hC hgrad).continuous).const_smul (2 : ℂ))
  · intro U
    change weightedTwoHilbertGradientContraction E g μ hμ h hh φ hφ (fun x => χ x ^ 2)
      (fun a => (hχ a).pow 2) (4 * C) (by positivity)
      (gradNormSq_cutoff_sq_le g.form χ hχ hχb C hC hgrad)
      (realizeWeightedTwoSection E g μ hμ h hh φ hφ U) =
      (2 : ℂ) • weightedOneCutoff E g μ hμ h hh φ hφ χ hχ hχb
        (weightedTwoHilbertGradientContraction E g μ hμ h hh φ hφ χ hχ C hC hgrad
          (realizeWeightedTwoSection E g μ hμ h hh φ hφ U))
    rw [weightedTwoHilbertGradientContraction_realize, weightedTwoHilbertGradientContraction_realize,
      weightedOneCutoff_realize]
    change (↑(weightedTwoGradientContractionSection E g μ hμ h hh φ hφ (fun x => χ x ^ 2)
      (fun a => (hχ a).pow 2) (4 * C) _ _ U) : WeightedOneHilbert E g μ hμ h hh φ hφ) =
      (2 : ℂ) • (↑(weightedOneCutoffSection E g μ hμ h hh φ hφ χ hχ hχb
        (weightedTwoGradientContractionSection E g μ hμ h hh φ hφ χ hχ C hC hgrad U)) :
          WeightedOneHilbert E g μ hμ h hh φ hφ)
    rw [← UniformSpace.Completion.coe_smul]
    congr 1
    apply Subtype.ext
    exact twoGradientContraction_cutoff_sq (r := r) E g.form χ hχ U.1

end Yau.LeafProofs.L14Aux
