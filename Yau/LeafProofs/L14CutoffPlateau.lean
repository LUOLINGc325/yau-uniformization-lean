import Yau.LeafProofs.L14TwoGraphCutoff

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

variable (g : Yau.SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
  (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)


theorem weightedTwoCutoff_realize_eq_of_one
    (θ : M.Carrier → ℝ) (hθ : SmoothFn θ) (hbθ : ∀ x,θ x ∈ Set.Icc (0 : ℝ) 1)
    (D : WeightedTwoSection E g μ hμ h hh φ hφ)
    (hone : ∀ x,D.1 x ≠ (0 : NQForm E 2) x → θ x = 1) :
    weightedTwoCutoff E g μ hμ h hh φ hφ θ hθ hbθ (realizeWeightedTwoSection E g μ hμ h hh φ hφ D) =
      realizeWeightedTwoSection E g μ hμ h hh φ hφ D := by
  rw [weightedTwoCutoff_realize]
  congr 1
  apply Subtype.ext
  funext x
  apply Subtype.ext
  change (θ x : ℂ) • (D.1 x).1 = (D.1 x).1
  by_cases hx : D.1 x = (0 : NQForm E 2) x
  · have hxv := congrArg Subtype.val hx
    change (D.1 x).1 = 0 at hxv
    rw [hxv,smul_zero]
  · rw [hone x hx,Complex.ofReal_one,one_smul]

theorem weightedOneCutoff_realize_eq_of_one
    (θ : M.Carrier → ℝ) (hθ : SmoothFn θ) (hbθ : ∀ x,θ x ∈ Set.Icc (0 : ℝ) 1)
    (D : WeightedOneSection E g μ hμ h hh φ hφ)
    (hone : ∀ x,D.1 x ≠ (0 : NQForm E 1) x → θ x = 1) :
    weightedOneCutoff E g μ hμ h hh φ hφ θ hθ hbθ (realizeWeightedOneSection E g μ hμ h hh φ hφ D) =
      realizeWeightedOneSection E g μ hμ h hh φ hφ D := by
  rw [weightedOneCutoff_realize]
  congr 1
  apply Subtype.ext
  funext x
  apply Subtype.ext
  change (θ x : ℂ) • (D.1 x).1 = (D.1 x).1
  by_cases hx : D.1 x = (0 : NQForm E 1) x
  · have hxv := congrArg Subtype.val hx
    change (D.1 x).1 = 0 at hxv
    rw [hxv,smul_zero]
  · rw [hone x hx,Complex.ofReal_one,one_smul]

theorem twoGradientContraction_zero_of_notMem_tsupport
    (χ : M.Carrier → ℝ) (W : NQForm E 2) (x : M.Carrier) (hx : x ∉ tsupport χ) :
    twoGradientContraction E g.form χ W x = (0 : NQForm E 1) x := by
  have hz : chartPt x x ∈ chartTarget x := mem_extChartAt_target x
  have hi : ContinuousAt (chartInv x) (chartPt x x) := continuousAt_extChartAt_symm'' (I := ComplexModel n) hz
  have ht : Tendsto (chartInv x) (𝓝 (chartPt x x)) (𝓝 x) := by
    simpa only [chartInv_chartPt_of_mem x x (mem_chart_source _ _)] using hi.tendsto
  have hχzero : χ =ᶠ[𝓝 x] (fun _ => 0) := by
    filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hx] with y hy
    exact image_eq_zero_of_notMem_tsupport hy
  have he : (fun w => Complex.ofReal (inChart x χ w)) =ᶠ[𝓝 (chartPt x x)] (fun _ => 0) := by
    filter_upwards [ht.eventually hχzero] with w hw
    simp only [inChart,hw,Complex.ofReal_zero]
  have hd : fderiv ℝ (fun w => Complex.ofReal (inChart x χ w)) (chartPt x x) = 0 := by
    rw [he.fderiv_eq (𝕜 := ℝ)]
    exact (hasFDerivAt_const (𝕜 := ℝ) (0 : ℂ) (chartPt x x)).fderiv
  apply Subtype.ext
  simp only [twoGradientContraction,chartScalarWirt,wirt,hd,
    zero_apply,zero_sub,neg_zero,zero_mul,mul_zero,Finset.sum_const_zero,zero_smul]
  rfl

theorem weightedTwoHilbertGradientContraction_cutoff_eq_of_one
    (χ θ : M.Carrier → ℝ) (hχ : SmoothFn χ) (hθ : SmoothFn θ)
    (hbθ : ∀ x,θ x ∈ Set.Icc (0 : ℝ) 1) (C : ℝ) (hC : 0 ≤ C)
    (hgrad : ∀ x,gradNormSq g.form χ x ≤ C)
    (hone : ∀ x ∈ tsupport χ,θ x = 1)
    (W : WeightedTwoHilbert E g μ hμ h hh φ hφ) :
    weightedTwoHilbertGradientContraction E g μ hμ h hh φ hφ χ hχ C hC hgrad
      (weightedTwoCutoff E g μ hμ h hh φ hφ θ hθ hbθ W) =
      weightedTwoHilbertGradientContraction E g μ hμ h hh φ hφ χ hχ C hC hgrad W := by
  rw [weightedTwoHilbertGradientContraction_cutoff]
  induction W using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih U =>
    change weightedOneCutoff E g μ hμ h hh φ hφ θ hθ hbθ
      (weightedTwoHilbertGradientContraction E g μ hμ h hh φ hφ χ hχ C hC hgrad (realizeWeightedTwoSection E g μ hμ h hh φ hφ U)) =
      weightedTwoHilbertGradientContraction E g μ hμ h hh φ hφ χ hχ C hC hgrad (realizeWeightedTwoSection E g μ hμ h hh φ hφ U)
    rw [weightedTwoHilbertGradientContraction_realize]
    apply weightedOneCutoff_realize_eq_of_one E g μ hμ h hh φ hφ θ hθ hbθ
    intro x hx
    exact hone x (by
      by_contra hn
      exact hx (twoGradientContraction_zero_of_notMem_tsupport E g χ U.1 x hn))


theorem weightedTwoCutoff_comp_eq_of_one
    (χ θ : M.Carrier → ℝ) (hχ : SmoothFn χ) (hθ : SmoothFn θ)
    (hbχ : ∀ x,χ x ∈ Set.Icc (0 : ℝ) 1) (hbθ : ∀ x,θ x ∈ Set.Icc (0 : ℝ) 1)
    (hone : ∀ x ∈ tsupport χ,θ x = 1)
    (W : WeightedTwoHilbert E g μ hμ h hh φ hφ) :
    weightedTwoCutoff E g μ hμ h hh φ hφ χ hχ hbχ
      (weightedTwoCutoff E g μ hμ h hh φ hφ θ hθ hbθ W) =
      weightedTwoCutoff E g μ hμ h hh φ hφ χ hχ hbχ W := by
  have hf : (fun x => χ x*θ x) = χ := by
    funext x
    by_cases hx : x ∈ tsupport χ
    · rw [hone x hx,mul_one]
    · rw [image_eq_zero_of_notMem_tsupport hx,zero_mul]
  simpa only [hf] using weightedTwoCutoff_mul E g μ hμ h hh φ hφ χ θ hχ hθ hbχ hbθ W

end Yau.LeafProofs.L14Aux
