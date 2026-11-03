import Yau.LeafProofs.L14TwoCutoff
import Yau.LeafProofs.L14TwoMultipliers
import Yau.LeafProofs.L14TwoLocalCoefficient

/-! Actual scalar and contraction coefficient formulas on weighted two-form
Hilbert completions. All local multiplier maps are bounded on the compact
coordinate set, so the raw formulas extend by density. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder ENNReal
open MeasureTheory Bundle Filter Module
namespace Yau.LeafProofs.L14Aux
open BundleDbar

/-- Multiplication in local L² by a continuous function on a compact set. -/
def compactLocalLpMultiply {n : ℕ} (K : Set (ComplexVector n)) (hK : IsCompact K)
    (c : ComplexVector n → ℂ) (hc : ContinuousOn c K)
    (f : Lp ℂ 2 ((lebesgueC n).restrict K)) : Lp ℂ 2 ((lebesgueC n).restrict K) :=
  (memLp_continuousOn_mul_compact K hK c f hc (Lp.memLp f)).toLp (fun z => c z * f z)

theorem compactLocalLpMultiply_ae {n : ℕ} (K : Set (ComplexVector n)) (hK : IsCompact K)
    (c : ComplexVector n → ℂ) (hc : ContinuousOn c K)
    (f : Lp ℂ 2 ((lebesgueC n).restrict K)) :
    compactLocalLpMultiply K hK c hc f =ᵐ[(lebesgueC n).restrict K] (fun z => c z * f z) :=
  MemLp.coeFn_toLp _

def compactLocalLpMultiplyLinear {n : ℕ} (K : Set (ComplexVector n)) (hK : IsCompact K)
    (c : ComplexVector n → ℂ) (hc : ContinuousOn c K) :
    Lp ℂ 2 ((lebesgueC n).restrict K) →ₗ[ℂ] Lp ℂ 2 ((lebesgueC n).restrict K) where
  toFun := compactLocalLpMultiply K hK c hc
  map_add' f g := by
    apply Lp.ext
    filter_upwards [compactLocalLpMultiply_ae K hK c hc (f+g),
      compactLocalLpMultiply_ae K hK c hc f, compactLocalLpMultiply_ae K hK c hc g,
      Lp.coeFn_add f g, Lp.coeFn_add (compactLocalLpMultiply K hK c hc f)
        (compactLocalLpMultiply K hK c hc g)] with z hfg hf hg ha hb
    simp only [hfg, hb, Pi.add_apply, ha, hf, hg, mul_add]
  map_smul' b f := by
    change compactLocalLpMultiply K hK c hc (b • f) = b • compactLocalLpMultiply K hK c hc f
    apply Lp.ext
    filter_upwards [compactLocalLpMultiply_ae K hK c hc (b • f),
      compactLocalLpMultiply_ae K hK c hc f, Lp.coeFn_smul b f,
      Lp.coeFn_smul b (compactLocalLpMultiply K hK c hc f)] with z hbf hf ha hb
    simp only [hbf, hb, Pi.smul_apply, ha, hf, smul_eq_mul]
    ring

def compactLocalLpMultiplyCLM {n : ℕ} (K : Set (ComplexVector n)) (hK : IsCompact K)
    (c : ComplexVector n → ℂ) (hc : ContinuousOn c K) :
    Lp ℂ 2 ((lebesgueC n).restrict K) →L[ℂ] Lp ℂ 2 ((lebesgueC n).restrict K) :=
  (compactLocalLpMultiplyLinear K hK c hc).mkContinuousOfExistsBound (by
    obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hc
    refine ⟨max B 0, fun f => ?_⟩
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [compactLocalLpMultiply_ae K hK c hc f,
      ae_restrict_mem hK.measurableSet] with z hz hzk
    change ‖compactLocalLpMultiply K hK c hc f z‖ ≤ _
    rw [hz, norm_mul]
    exact mul_le_mul_of_nonneg_right ((hB z hzk).trans (le_max_left _ _)) (norm_nonneg _))

theorem compactLocalLpMultiplyCLM_ae {n : ℕ} (K : Set (ComplexVector n)) (hK : IsCompact K)
    (c : ComplexVector n → ℂ) (hc : ContinuousOn c K)
    (f : Lp ℂ 2 ((lebesgueC n).restrict K)) :
    compactLocalLpMultiplyCLM K hK c hc f =ᵐ[(lebesgueC n).restrict K] (fun z => c z * f z) :=
  compactLocalLpMultiply_ae K hK c hc f

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)] [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]
variable (g : Yau.SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
  (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
  (a : M.Carrier) (K : Set (ComplexVector n)) (hK : IsCompact K)
  (hsub : K ⊆ localDomain (r := r) E a)

def localRealScalarLpMultiplier (χ : M.Carrier → ℝ) (hχ : SmoothFn χ) :
    Lp ℂ 2 ((lebesgueC n).restrict K) →L[ℂ] Lp ℂ 2 ((lebesgueC n).restrict K) :=
  compactLocalLpMultiplyCLM K hK (fun z => (χ (chartInv a z) : ℂ))
    ((((hχ a).continuousLinearMap_comp Complex.ofRealCLM).continuousOn).mono
      (hsub.trans Set.inter_subset_left))

omit [∀ x, IsScalarTower ℝ ℂ (E x)] [VectorBundle ℂ (ComplexVector r) E] in
theorem localRealScalarLpMultiplier_ae (χ : M.Carrier → ℝ) (hχ : SmoothFn χ)
    (f : Lp ℂ 2 ((lebesgueC n).restrict K)) :
    localRealScalarLpMultiplier E a K hK hsub χ hχ f =ᵐ[(lebesgueC n).restrict K]
      (fun z => (χ (chartInv a z) : ℂ) * f z) :=
  compactLocalLpMultiplyCLM_ae K hK _ _ f

/-- The actual scalar local coefficient identity holds at every completion point. -/
theorem weightedTwoHilbertLocalCoefficient_multiplier
    (p : TwoCoefficientIndex n r) (χ : M.Carrier → ℝ) (hχ : SmoothFn χ)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ x, χ x ^ 2 ≤ C ^ 2)
    (W : WeightedTwoHilbert E g μ hμ h hh φ hφ) :
    weightedTwoHilbertLocalCoefficient E g μ hμ h hh φ hφ a K hK hsub p
      (weightedTwoMultiplier E g μ hμ h hh φ hφ χ hχ C hC hbound W) =
    localRealScalarLpMultiplier E a K hK hsub χ hχ
      (weightedTwoHilbertLocalCoefficient E g μ hμ h hh φ hφ a K hK hsub p W) := by
  refine UniformSpace.Completion.induction_on W (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro U
  change weightedTwoHilbertLocalCoefficient E g μ hμ h hh φ hφ a K hK hsub p
      (weightedTwoMultiplier E g μ hμ h hh φ hφ χ hχ C hC hbound
        (realizeWeightedTwoSection E g μ hμ h hh φ hφ U)) =
    localRealScalarLpMultiplier E a K hK hsub χ hχ
      (weightedTwoHilbertLocalCoefficient E g μ hμ h hh φ hφ a K hK hsub p
        (realizeWeightedTwoSection E g μ hμ h hh φ hφ U))
  rw [weightedTwoMultiplier_realize, weightedTwoHilbertLocalCoefficient_realize,
    weightedTwoHilbertLocalCoefficient_realize]
  apply Lp.ext
  filter_upwards [weightedTwoLocalCoefficient_ae E g μ hμ h hh φ hφ a K hK hsub p
      (weightedTwoMultiplierSection E g μ hμ h hh φ hφ χ hχ C hC hbound U),
    localRealScalarLpMultiplier_ae E a K hK hsub χ hχ
      (weightedTwoLocalCoefficient E g μ hμ h hh φ hφ a K hK hsub p U),
    weightedTwoLocalCoefficient_ae E g μ hμ h hh φ hφ a K hK hsub p U] with z hleft hright hu
  rw [hleft, hright, hu]
  exact coefficients_multiplyForm E (fun x => (χ x : ℂ)) U.1 a z ![p.1.2,p.2] p.1.1

theorem weightedTwoHilbertLocalCoefficient_multiplier_ae
    (p : TwoCoefficientIndex n r) (χ : M.Carrier → ℝ) (hχ : SmoothFn χ)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ x, χ x ^ 2 ≤ C ^ 2)
    (W : WeightedTwoHilbert E g μ hμ h hh φ hφ) :
    weightedTwoHilbertLocalCoefficient E g μ hμ h hh φ hφ a K hK hsub p
      (weightedTwoMultiplier E g μ hμ h hh φ hφ χ hχ C hC hbound W) =ᵐ[(lebesgueC n).restrict K]
      (fun z => (χ (chartInv a z) : ℂ) *
        weightedTwoHilbertLocalCoefficient E g μ hμ h hh φ hφ a K hK hsub p W z) := by
  rw [weightedTwoHilbertLocalCoefficient_multiplier E g μ hμ h hh φ hφ a K hK hsub]
  exact localRealScalarLpMultiplier_ae E a K hK hsub χ hχ _


/-- Each coefficient of the local contraction matrix acts boundedly on local L². -/
def localTwoContractionLpMultiplier (χ : M.Carrier → ℝ) (hχ : SmoothFn χ)
    (i k : Fin n) :
    Lp ℂ 2 ((lebesgueC n).restrict K) →L[ℂ] Lp ℂ 2 ((lebesgueC n).restrict K) :=
  compactLocalLpMultiplyCLM K hK
    (fun z => star (wirtBar (fun w => Complex.ofReal (inChart a χ w)) z (stdVec i)) *
      (hMat g.form a z)⁻¹ i k) (by
    have hc : ContDiffOn ℝ ∞ (fun w => Complex.ofReal (inChart a χ w))
        (localDomain (r := r) E a) :=
      ((hχ a).continuousLinearMap_comp Complex.ofRealCLM).mono Set.inter_subset_left
    have hm := (wirt_contDiffOn (localDomain_isOpen E a) _ hc (stdVec i)).mul
      ((L18Aux.hMat_inverse_contDiffOn g a i k).mono Set.inter_subset_left)
    simpa only [star_wirtBar_ofReal] using hm.continuousOn.mono hsub)

theorem localTwoContractionLpMultiplier_ae (χ : M.Carrier → ℝ) (hχ : SmoothFn χ)
    (i k : Fin n) (f : Lp ℂ 2 ((lebesgueC n).restrict K)) :
    localTwoContractionLpMultiplier E g a K hK hsub χ hχ i k f =ᵐ[(lebesgueC n).restrict K]
      (fun z => star (wirtBar (fun w => Complex.ofReal (inChart a χ w)) z (stdVec i)) *
        (hMat g.form a z)⁻¹ i k * f z) :=
  compactLocalLpMultiplyCLM_ae K hK _ _ f

def localTwoContractionLpSum (χ : M.Carrier → ℝ) (hχ : SmoothFn χ) (j : Fin n) (α : Fin r) :
    WeightedTwoHilbert E g μ hμ h hh φ hφ →L[ℂ] Lp ℂ 2 ((lebesgueC n).restrict K) :=
  ∑ i, ∑ k, (localTwoContractionLpMultiplier E g a K hK hsub χ hχ i k).comp
    (weightedTwoHilbertLocalCoefficient E g μ hμ h hh φ hφ a K hK hsub ((α,k),j))

theorem localTwoContractionLpSum_ae
    (χ : M.Carrier → ℝ) (hχ : SmoothFn χ) (j : Fin n) (α : Fin r)
    (W : WeightedTwoHilbert E g μ hμ h hh φ hφ) :
    localTwoContractionLpSum E g μ hμ h hh φ hφ a K hK hsub χ hχ j α W =ᵐ[(lebesgueC n).restrict K]
      (fun z => ∑ i, ∑ k,
        star (wirtBar (fun w => Complex.ofReal (inChart a χ w)) z (stdVec i)) *
          (hMat g.form a z)⁻¹ i k *
            weightedTwoHilbertLocalCoefficient E g μ hμ h hh φ hφ a K hK hsub ((α,k),j) W z) := by
  let f := fun i k => localTwoContractionLpMultiplier E g a K hK hsub χ hχ i k
    (weightedTwoHilbertLocalCoefficient E g μ hμ h hh φ hφ a K hK hsub ((α,k),j) W)
  simp only [localTwoContractionLpSum, sum_apply, ContinuousLinearMap.comp_apply]
  change (∑ i, ∑ k, f i k : Lp ℂ 2 ((lebesgueC n).restrict K)) =ᵐ[(lebesgueC n).restrict K] _
  have hmul := ae_all_iff.mpr (fun i => ae_all_iff.mpr (fun k =>
    localTwoContractionLpMultiplier_ae E g a K hK hsub χ hχ i k
      (weightedTwoHilbertLocalCoefficient E g μ hμ h hh φ hφ a K hK hsub ((α,k),j) W)))
  have hinner := ae_all_iff.mpr (fun i => Lp.coeFn_finsetSum Finset.univ (f i))
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun i => ∑ k, f i k), hinner, hmul]
    with z hsum hinnerz hmulz
  simp only [Finset.sum_apply] at hsum hinnerz
  rw [hsum]
  apply Finset.sum_congr rfl
  intro i _
  rw [hinnerz i]
  apply Finset.sum_congr rfl
  intro k _
  exact hmulz i k

/-- Local contraction coefficients on the Hilbert completion are the genuine
smooth matrix multiplier applied to the two-form's local coefficients. -/
theorem weightedTwoHilbertLocalCoefficient_gradientContraction
    (χ : M.Carrier → ℝ) (hχ : SmoothFn χ) (C : ℝ) (hC : 0 ≤ C)
    (hgrad : ∀ x, gradNormSq g.form χ x ≤ C) (j : Fin n) (α : Fin r)
    (W : WeightedTwoHilbert E g μ hμ h hh φ hφ) :
    weightedOneHilbertLocalCoefficient E g μ hμ h hh φ hφ a K hK hsub j α
      (weightedTwoHilbertGradientContraction E g μ hμ h hh φ hφ χ hχ C hC hgrad W) =
    localTwoContractionLpSum E g μ hμ h hh φ hφ a K hK hsub χ hχ j α W := by
  refine UniformSpace.Completion.induction_on W (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro U
  change weightedOneHilbertLocalCoefficient E g μ hμ h hh φ hφ a K hK hsub j α
      (weightedTwoHilbertGradientContraction E g μ hμ h hh φ hφ χ hχ C hC hgrad
        (realizeWeightedTwoSection E g μ hμ h hh φ hφ U)) =
    localTwoContractionLpSum E g μ hμ h hh φ hφ a K hK hsub χ hχ j α
      (realizeWeightedTwoSection E g μ hμ h hh φ hφ U)
  rw [weightedTwoHilbertGradientContraction_realize]
  apply Lp.ext
  have hcoeff := ae_all_iff.mpr (fun k => weightedTwoHilbertLocalCoefficient_realize_ae
    E g μ hμ h hh φ hφ a K hK hsub ((α,k),j) U)
  filter_upwards [weightedOneHilbertLocalCoefficient_realize_ae E g μ hμ h hh φ hφ
      a K hK hsub j α (weightedTwoGradientContractionSection E g μ hμ h hh φ hφ χ hχ C hC hgrad U),
    localTwoContractionLpSum_ae E g μ hμ h hh φ hφ a K hK hsub χ hχ j α
      (realizeWeightedTwoSection E g μ hμ h hh φ hφ U),
    hcoeff, ae_restrict_mem hK.measurableSet] with z hleft hright hcoeffz hz
  rw [hleft, hright]
  change coefficients (r := r) E (twoGradientContraction E g.form χ U.1) a z (fun _ => j) α = _
  rw [coefficients_twoGradientContraction_apply E g.form χ hχ U.1 a z (hsub hz) j α]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  rw [hcoeffz k]

theorem weightedTwoHilbertLocalCoefficient_gradientContraction_ae
    (χ : M.Carrier → ℝ) (hχ : SmoothFn χ) (C : ℝ) (hC : 0 ≤ C)
    (hgrad : ∀ x, gradNormSq g.form χ x ≤ C) (j : Fin n) (α : Fin r)
    (W : WeightedTwoHilbert E g μ hμ h hh φ hφ) :
    weightedOneHilbertLocalCoefficient E g μ hμ h hh φ hφ a K hK hsub j α
      (weightedTwoHilbertGradientContraction E g μ hμ h hh φ hφ χ hχ C hC hgrad W) =ᵐ[(lebesgueC n).restrict K]
      (fun z => ∑ i, ∑ k,
        star (wirtBar (fun w => Complex.ofReal (inChart a χ w)) z (stdVec i)) *
          (hMat g.form a z)⁻¹ i k *
            weightedTwoHilbertLocalCoefficient E g μ hμ h hh φ hφ a K hK hsub ((α,k),j) W z) := by
  rw [weightedTwoHilbertLocalCoefficient_gradientContraction E g μ hμ h hh φ hφ a K hK hsub]
  exact localTwoContractionLpSum_ae E g μ hμ h hh φ hφ a K hK hsub χ hχ j α W


theorem weightedTwoHilbertLocalCoefficient_cutoff
    (p : TwoCoefficientIndex n r) (χ : M.Carrier → ℝ) (hχ : SmoothFn χ)
    (hbound : ∀ x, χ x ∈ Set.Icc (0 : ℝ) 1)
    (W : WeightedTwoHilbert E g μ hμ h hh φ hφ) :
    weightedTwoHilbertLocalCoefficient E g μ hμ h hh φ hφ a K hK hsub p
      (weightedTwoCutoff E g μ hμ h hh φ hφ χ hχ hbound W) =
    localRealScalarLpMultiplier E a K hK hsub χ hχ
      (weightedTwoHilbertLocalCoefficient E g μ hμ h hh φ hφ a K hK hsub p W) :=
  weightedTwoHilbertLocalCoefficient_multiplier E g μ hμ h hh φ hφ a K hK hsub p χ hχ 1 zero_le_one _ W

theorem weightedTwoHilbertLocalCoefficient_cutoff_ae
    (p : TwoCoefficientIndex n r) (χ : M.Carrier → ℝ) (hχ : SmoothFn χ)
    (hbound : ∀ x, χ x ∈ Set.Icc (0 : ℝ) 1)
    (W : WeightedTwoHilbert E g μ hμ h hh φ hφ) :
    weightedTwoHilbertLocalCoefficient E g μ hμ h hh φ hφ a K hK hsub p
      (weightedTwoCutoff E g μ hμ h hh φ hφ χ hχ hbound W) =ᵐ[(lebesgueC n).restrict K]
      (fun z => (χ (chartInv a z) : ℂ) *
        weightedTwoHilbertLocalCoefficient E g μ hμ h hh φ hφ a K hK hsub p W z) :=
  weightedTwoHilbertLocalCoefficient_multiplier_ae E g μ hμ h hh φ hφ a K hK hsub p χ hχ 1 zero_le_one _ W

end Yau.LeafProofs.L14Aux
