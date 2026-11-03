import Yau.LeafProofs.L14TwoL2
import Yau.LeafProofs.L14TwoContraction

set_option backward.isDefEq.respectTransparency false
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

theorem locallyL2_twoGradientContraction (g : Yau.SmoothMetric M)
    (χ : M.Carrier → ℝ) (hχ : SmoothFn χ) (W : NQForm E 2) (hW : LocallyL2 (r := r) E W) :
    LocallyL2 (r := r) E (twoGradientContraction E g.form χ W) := by
  intro a I α
  let j := I 0
  have hI : I = (fun _ => j) := funext fun t => congrArg I (Subsingleton.elim t 0)
  rw [hI]
  let O := localDomain (r := r) E a
  let C := fun i k z => wirt (fun w => Complex.ofReal (inChart a χ w)) z (stdVec i) * (hMat g.form a z)⁻¹ i k
  have hχC : ContDiffOn ℝ ∞ (fun w => Complex.ofReal (inChart a χ w)) O :=
    ((hχ a).continuousLinearMap_comp Complex.ofRealCLM).mono Set.inter_subset_left
  have hC (i k : Fin n) : ContDiffOn ℝ ∞ (C i k) O :=
    (wirt_contDiffOn (localDomain_isOpen E a) _ hχC (stdVec i)).mul
      ((L18Aux.hMat_inverse_contDiffOn g a i k).mono Set.inter_subset_left)
  have hcoeff (z : ComplexVector n) (hz : z ∈ O) :
      coefficients (r := r) E (twoGradientContraction E g.form χ W) a z (fun _ => j) α =
      ∑ i, ∑ k, C i k z * coefficients (r := r) E W a z ![k,j] α := by
    simpa only [C, star_wirtBar_ofReal, mul_assoc] using
      coefficients_twoGradientContraction_apply E g.form χ hχ W a z hz j α
  refine ⟨?_, ?_⟩
  · have hm : AEStronglyMeasurable (fun z => ∑ i, ∑ k,
        C i k z * coefficients (r := r) E W a z ![k,j] α) ((lebesgueC n).restrict O) :=
      Finset.univ.aestronglyMeasurable_fun_sum (fun i _ =>
        Finset.univ.aestronglyMeasurable_fun_sum (fun k _ =>
          ((hC i k).continuousOn.aestronglyMeasurable (localDomain_isOpen E a).measurableSet).mul (hW a ![k,j] α).1))
    apply hm.congr
    filter_upwards [ae_restrict_mem (localDomain_isOpen E a).measurableSet] with z hz
    exact (hcoeff z hz).symm
  · intro K hK hs
    have ht (i k : Fin n) : MemLp (fun z => C i k z * coefficients (r := r) E W a z ![k,j] α)
        2 ((lebesgueC n).restrict K) := memLp_continuousOn_mul_compact K hK _ _
      ((hC i k).continuousOn.mono hs) (locallyL2_coefficients_memLp E W hW a ![k,j] α K hK hs)
    have hm : MemLp (fun z => ∑ i, ∑ k, C i k z * coefficients (r := r) E W a z ![k,j] α)
        2 ((lebesgueC n).restrict K) :=
      memLp_finsetSum Finset.univ (fun i _ => memLp_finsetSum Finset.univ (fun k _ => ht i k))
    have hmp : MemLp (fun z => coefficients (r := r) E (twoGradientContraction E g.form χ W)
        a z (fun _ => j) α) 2 ((lebesgueC n).restrict K) := MemLp.ae_eq
      ((ae_restrict_mem hK.measurableSet).mono fun z hz => (hcoeff z (hs hz)).symm) hm
    exact lintegral_norm_sq_lt_top_of_memLp hmp

theorem weightedNormSq_twoGradientContraction_le (g : HermitianField M) (μ : Measure M.Carrier)
    (h : Metric E) (φ : M.Carrier → ℝ) (χ : M.Carrier → ℝ) (hχ : SmoothFn χ)
    (W : NQForm E 2) (C : ℝ) (hC : 0 ≤ C) (hgrad : ∀ x, gradNormSq g χ x ≤ C) :
    weightedNormSq (r := r) E g h μ φ (twoGradientContraction E g χ W) ≤
      ENNReal.ofReal (2 * C) * weightedNormSq (r := r) E g h μ φ W := by
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal ((2 * C) * (BundleDbar.formNormSq (r := r) E g h W x * Real.exp (-φ x))) ∂μ := by
      apply lintegral_mono
      intro x
      change ENNReal.ofReal (BundleDbar.formNormSq (r := r) E g h
        (twoGradientContraction E g χ W) x * Real.exp (-φ x)) ≤ _
      apply ENNReal.ofReal_le_ofReal
      have he := (twoGradientContraction_normSq_le (r := r) E g h χ hχ W x).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hgrad x) (by norm_num))
          (formNormSq_two_nonneg (r := r) E g h W x))
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right he (Real.exp_pos _).le
    _ = _ := by
      simp only [ENNReal.ofReal_mul (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hC)]
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

theorem weightedL2_twoGradientContraction (g : Yau.SmoothMetric M) (μ : Measure M.Carrier)
    (h : Metric E) (φ : M.Carrier → ℝ) (χ : M.Carrier → ℝ) (hχ : SmoothFn χ)
    (W : NQForm E 2) (hW : WeightedL2 (r := r) E g.form h μ φ W)
    (C : ℝ) (hC : 0 ≤ C) (hgrad : ∀ x, gradNormSq g.form χ x ≤ C) :
    WeightedL2 (r := r) E g.form h μ φ (twoGradientContraction E g.form χ W) :=
  ⟨locallyL2_twoGradientContraction (r := r) E g χ hχ W hW.1,
    (weightedNormSq_twoGradientContraction_le (r := r) E g.form μ h φ χ hχ W C hC hgrad).trans_lt
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hW.2)⟩

theorem oneForm_ext_of_coefficients (u v : NQForm E 1)
    (he : ∀ a z, z ∈ localDomain (r := r) E a → ∀ i α,
      coefficients (r := r) E u a z (fun _ => i) α = coefficients (r := r) E v a z (fun _ => i) α) : u = v := by
  funext x
  let hx : x ∈ bundleChartSource (r := r) E x :=
    ⟨mem_extChartAt_source x, FiberBundle.mem_baseSet_trivializationAt' x⟩
  have hz : chartPt x x ∈ localDomain (r := r) E x := by
    refine ⟨mem_extChartAt_target x, ?_⟩
    change chartInv x (chartPt x x) ∈ (localTriv (r := r) E x).baseSet
    rw [chartInv_chartPt_of_mem x x (mem_chart_source _ _)]
    exact hx.2
  apply oneTensorCoordinates_injective E x x hx
  ext p
  rcases p with ⟨i, α⟩
  rw [oneTensorCoordinates_at_chartPt E u x x hx i α, oneTensorCoordinates_at_chartPt E v x x hx i α]
  exact he x (chartPt x x) hz i α

include r in
theorem twoGradientContraction_add (g : HermitianField M) (χ : M.Carrier → ℝ) (hχ : SmoothFn χ)
    (W Z : NQForm E 2) : twoGradientContraction E g χ (W + Z) =
      twoGradientContraction E g χ W + twoGradientContraction E g χ Z := by
  apply oneForm_ext_of_coefficients (r := r) E
  intro a z hz j α
  simp only [coefficients_twoGradientContraction_apply E g χ hχ _ a z hz,
    coefficients_add, mul_add, Finset.sum_add_distrib]

include r in
theorem twoGradientContraction_smul (g : HermitianField M) (χ : M.Carrier → ℝ) (hχ : SmoothFn χ)
    (c : ℂ) (W : NQForm E 2) : twoGradientContraction E g χ (c • W) = c • twoGradientContraction E g χ W := by
  apply oneForm_ext_of_coefficients (r := r) E
  intro a z hz j α
  rw [coefficients_twoGradientContraction_apply E g χ hχ _ a z hz, coefficients_smul,
    coefficients_twoGradientContraction_apply E g χ hχ _ a z hz]
  simp_rw [coefficients_smul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  ring

variable (g : Yau.SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
  (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)

def weightedTwoGradientContractionSection (χ : M.Carrier → ℝ) (hχ : SmoothFn χ)
    (C : ℝ) (hC : 0 ≤ C) (hgrad : ∀ x, gradNormSq g.form χ x ≤ C)
    (W : WeightedTwoSection E g μ hμ h hh φ hφ) : WeightedOneSection E g μ hμ h hh φ hφ :=
  ⟨twoGradientContraction E g.form χ W.1, weightedL2_twoGradientContraction E g μ h φ χ hχ W.1 W.2 C hC hgrad⟩

theorem weightedTwoGradientContractionSection_norm_sq_le
    (χ : M.Carrier → ℝ) (hχ : SmoothFn χ) (C : ℝ) (hC : 0 ≤ C)
    (hgrad : ∀ x, gradNormSq g.form χ x ≤ C) (W : WeightedTwoSection E g μ hμ h hh φ hφ) :
    ‖realizeWeightedOneSection E g μ hμ h hh φ hφ
      (weightedTwoGradientContractionSection E g μ hμ h hh φ hφ χ hχ C hC hgrad W)‖ ^ 2 ≤ (2 * C) * ‖W‖ ^ 2 := by
  have he := weightedNormSq_twoGradientContraction_le (r := r) E g.form μ h φ χ hχ W.1 C hC hgrad
  have hfinite : ENNReal.ofReal (2 * C) * weightedNormSq (r := r) E g.form h μ φ W.1 ≠ ⊤ :=
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top W.2.2).ne
  have ht := ENNReal.toReal_mono hfinite he
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (mul_nonneg (by norm_num) hC)] at ht
  rw [realizeWeightedOneSection_norm_sq, weightedTwoSection_norm_sq]
  exact ht

def weightedTwoGradientContractionLinear (χ : M.Carrier → ℝ) (hχ : SmoothFn χ)
    (C : ℝ) (hC : 0 ≤ C) (hgrad : ∀ x, gradNormSq g.form χ x ≤ C) :
    WeightedTwoSection E g μ hμ h hh φ hφ →ₗ[ℂ] WeightedOneSection E g μ hμ h hh φ hφ where
  toFun := weightedTwoGradientContractionSection E g μ hμ h hh φ hφ χ hχ C hC hgrad
  map_add' W Z := by
    apply Subtype.ext
    exact twoGradientContraction_add (r := r) E g.form χ hχ W.1 Z.1
  map_smul' c W := by
    apply Subtype.ext
    exact twoGradientContraction_smul (r := r) E g.form χ hχ c W.1

def weightedTwoGradientContractionCLM (χ : M.Carrier → ℝ) (hχ : SmoothFn χ)
    (C : ℝ) (hC : 0 ≤ C) (hgrad : ∀ x, gradNormSq g.form χ x ≤ C) :
    WeightedTwoSection E g μ hμ h hh φ hφ →L[ℂ] WeightedOneHilbert E g μ hμ h hh φ hφ :=
  ((UniformSpace.Completion.toComplL : WeightedOneSection E g μ hμ h hh φ hφ →L[ℂ]
    WeightedOneHilbert E g μ hμ h hh φ hφ).toLinearMap.comp
      (weightedTwoGradientContractionLinear E g μ hμ h hh φ hφ χ hχ C hC hgrad)).mkContinuous
        (Real.sqrt (2 * C)) (by
      intro W
      have he := weightedTwoGradientContractionSection_norm_sq_le E g μ hμ h hh φ hφ χ hχ C hC hgrad W
      apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg W))).mp
      calc
        _ ≤ (2 * C) * ‖W‖ ^ 2 := he
        _ = (Real.sqrt (2 * C) * ‖W‖) ^ 2 := by rw [mul_pow, Real.sq_sqrt (mul_nonneg (by norm_num) hC)])

def weightedTwoHilbertGradientContraction (χ : M.Carrier → ℝ) (hχ : SmoothFn χ)
    (C : ℝ) (hC : 0 ≤ C) (hgrad : ∀ x, gradNormSq g.form χ x ≤ C) :
    WeightedTwoHilbert E g μ hμ h hh φ hφ →L[ℂ] WeightedOneHilbert E g μ hμ h hh φ hφ :=
  (weightedTwoGradientContractionCLM E g μ hμ h hh φ hφ χ hχ C hC hgrad).fromCompletion

theorem weightedTwoHilbertGradientContraction_realize (χ : M.Carrier → ℝ) (hχ : SmoothFn χ)
    (C : ℝ) (hC : 0 ≤ C) (hgrad : ∀ x, gradNormSq g.form χ x ≤ C)
    (W : WeightedTwoSection E g μ hμ h hh φ hφ) :
    weightedTwoHilbertGradientContraction E g μ hμ h hh φ hφ χ hχ C hC hgrad
      (realizeWeightedTwoSection E g μ hμ h hh φ hφ W) =
      realizeWeightedOneSection E g μ hμ h hh φ hφ
        (weightedTwoGradientContractionSection E g μ hμ h hh φ hφ χ hχ C hC hgrad W) :=
  ContinuousLinearMap.fromCompletion_apply_coe _ W

theorem weightedTwoHilbertGradientContraction_norm_sq_le
    (χ : M.Carrier → ℝ) (hχ : SmoothFn χ) (C : ℝ) (hC : 0 ≤ C)
    (hgrad : ∀ x, gradNormSq g.form χ x ≤ C) (W : WeightedTwoHilbert E g μ hμ h hh φ hφ) :
    ‖weightedTwoHilbertGradientContraction E g μ hμ h hh φ hφ χ hχ C hC hgrad W‖ ^ 2 ≤ (2 * C) * ‖W‖ ^ 2 := by
  refine UniformSpace.Completion.induction_on W (isClosed_le (by fun_prop) (by fun_prop)) ?_
  intro V
  change ‖weightedTwoHilbertGradientContraction E g μ hμ h hh φ hφ χ hχ C hC hgrad
    (realizeWeightedTwoSection E g μ hμ h hh φ hφ V)‖ ^ 2 ≤ (2 * C) * ‖(V : UniformSpace.Completion (WeightedTwoSection E g μ hμ h hh φ hφ))‖ ^ 2
  rw [weightedTwoHilbertGradientContraction_realize, UniformSpace.Completion.norm_coe]
  exact weightedTwoGradientContractionSection_norm_sq_le E g μ hμ h hh φ hφ χ hχ C hC hgrad V

end Yau.LeafProofs.L14Aux
