import Yau.LeafProofs.L14GlobalTwoAdjoint
import Yau.LeafProofs.L14OneCompactDensity
import Yau.LeafProofs.L14Wedge
import Yau.LeafProofs.L14TwoCutoffAlgebra

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

variable (hE : Holomorphic (r := r) E)
include hE in
theorem weightedTwoAdjointGraph_zero_left
    (R : WeightedOneHilbert E g μ hμ h hh φ hφ)
    (hR : (0,R) ∈ weightedTwoAdjointGraph E g μ hμ h hh φ hφ) : R = 0 := by
  apply weightedOneHilbert_eq_zero_of_chart_tests_left E g μ hμ h hh φ hφ hE R
  intro a F hF hc hs
  have hp := oneFormPushforward_maximalDbarGraph E g μ hμ h hh φ hφ hE a F hF hc hs
  let D : WeightedTwoSection E g μ hμ h hh φ hφ := ⟨twoFormPushforward E a (modelOneDbar F),hp.2.1⟩
  have he := hR (weightedOneChartSection E g μ hμ h hh φ hφ hE a F hF hc hs) D hp.2.2
  simpa only [inner_zero_right] using he.symm

include hE in
theorem weightedTwoAdjointGraph_single_valued
    (W : WeightedTwoHilbert E g μ hμ h hh φ hφ)
    (R S : WeightedOneHilbert E g μ hμ h hh φ hφ)
    (hR : (W,R) ∈ weightedTwoAdjointGraph E g μ hμ h hh φ hφ)
    (hS : (W,S) ∈ weightedTwoAdjointGraph E g μ hμ h hh φ hφ) : R = S := by
  have he := Submodule.sub_mem (weightedTwoAdjointGraph E g μ hμ h hh φ hφ) hR hS
  change (W-W,R-S) ∈ weightedTwoAdjointGraph E g μ hμ h hh φ hφ at he
  rw [sub_self] at he
  exact sub_eq_zero.mp (weightedTwoAdjointGraph_zero_left E g μ hμ h hh φ hφ hE (R-S) he)

def weightedGradientWedgeSection
    (χ : M.Carrier → ℝ) (hχ : SmoothFn χ) (C : ℝ) (hC : 0 ≤ C)
    (hgrad : ∀ x,gradNormSq g.form χ x ≤ C)
    (U : WeightedOneSection E g μ hμ h hh φ hφ) : WeightedTwoSection E g μ hμ h hh φ hφ :=
  ⟨gradientWedge E χ U.1,weightedL2_gradientWedge E g.form μ h φ χ hχ U.1 U.2 C hC hgrad⟩

theorem weightedGradientWedge_inner
    (χ : M.Carrier → ℝ) (hχ : SmoothFn χ) (C : ℝ) (hC : 0 ≤ C)
    (hgrad : ∀ x,gradNormSq g.form χ x ≤ C)
    (U : WeightedOneSection E g μ hμ h hh φ hφ)
    (W : WeightedTwoHilbert E g μ hμ h hh φ hφ) :
    inner ℂ (realizeWeightedTwoSection E g μ hμ h hh φ hφ
      (weightedGradientWedgeSection E g μ hμ h hh φ hφ χ hχ C hC hgrad U)) W =
      inner ℂ (realizeWeightedOneSection E g μ hμ h hh φ hφ U)
        (weightedTwoHilbertGradientContraction E g μ hμ h hh φ hφ χ hχ C hC hgrad W) := by
  induction W using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih V =>
    change inner ℂ _ (realizeWeightedTwoSection E g μ hμ h hh φ hφ V) = inner ℂ (realizeWeightedOneSection E g μ hμ h hh φ hφ U) (weightedTwoHilbertGradientContraction E g μ hμ h hh φ hφ χ hχ C hC hgrad (realizeWeightedTwoSection E g μ hμ h hh φ hφ V))
    rw [weightedTwoHilbertGradientContraction_realize,realizeWeightedTwoSection_inner,realizeWeightedOneSection_inner]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      change twoFormPairing E g.form h (gradientWedge E χ U.1) V.1 x * _ =
        oneFormPairing E g.form h U.1 (twoGradientContraction E g.form χ V.1) x * _
      rw [gradientWedge_pairing (r := r) E g.form h χ hχ U.1 V.1 x]


theorem oneFormPairing_multiply_real (χ : M.Carrier → ℝ)
    (u v : NQForm E 1) (x : M.Carrier) :
    oneFormPairing E g.form h (multiplyForm E (fun x => (χ x : ℂ)) u) v x =
      oneFormPairing E g.form h u (multiplyForm E (fun x => (χ x : ℂ)) v) x := by
  change oneTensorFramePairing (g.form x) (h x) _ _ ((χ x : ℂ) • (u x).1) (v x).1 =
    oneTensorFramePairing (g.form x) (h x) _ _ (u x).1 ((χ x : ℂ) • (v x).1)
  rw [oneTensorFramePairing_smul_left,oneTensorFramePairing_smul_right]
  simp

theorem weightedOneCutoff_inner (χ : M.Carrier → ℝ) (hχ : SmoothFn χ)
    (hbound : ∀ x,χ x ∈ Set.Icc (0 : ℝ) 1)
    (W V : WeightedOneHilbert E g μ hμ h hh φ hφ) :
    inner ℂ (weightedOneCutoff E g μ hμ h hh φ hφ χ hχ hbound W) V =
      inner ℂ W (weightedOneCutoff E g μ hμ h hh φ hφ χ hχ hbound V) := by
  induction W using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih U =>
    induction V using UniformSpace.Completion.induction_on with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih Z =>
      change inner ℂ (weightedOneCutoff E g μ hμ h hh φ hφ χ hχ hbound
        (realizeWeightedOneSection E g μ hμ h hh φ hφ U))
        (realizeWeightedOneSection E g μ hμ h hh φ hφ Z) =
        inner ℂ (realizeWeightedOneSection E g μ hμ h hh φ hφ U)
          (weightedOneCutoff E g μ hμ h hh φ hφ χ hχ hbound
            (realizeWeightedOneSection E g μ hμ h hh φ hφ Z))
      rw [weightedOneCutoff_realize,weightedOneCutoff_realize,realizeWeightedOneSection_inner,realizeWeightedOneSection_inner]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => congrArg (fun c : ℂ => c*(Real.exp (-φ x) : ℂ))
        (oneFormPairing_multiply_real E g h χ U.1 Z.1 x)

theorem weightedOneCutoff_mul (χ η : M.Carrier → ℝ) (hχ : SmoothFn χ) (hη : SmoothFn η)
    (hχb : ∀ x, χ x ∈ Set.Icc (0 : ℝ) 1) (hηb : ∀ x, η x ∈ Set.Icc (0 : ℝ) 1)
    (W : WeightedOneHilbert E g μ hμ h hh φ hφ) :
    weightedOneCutoff E g μ hμ h hh φ hφ χ hχ hχb
      (weightedOneCutoff E g μ hμ h hh φ hφ η hη hηb W) =
      weightedOneCutoff E g μ hμ h hh φ hφ (fun x => χ x * η x)
        (fun a => (hχ a).mul (hη a)) (cutoff_mul_mem_Icc χ η hχb hηb) W := by
  induction W using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih U =>
    change weightedOneCutoff E g μ hμ h hh φ hφ χ hχ hχb
      (weightedOneCutoff E g μ hμ h hh φ hφ η hη hηb
        (realizeWeightedOneSection E g μ hμ h hh φ hφ U)) =
      weightedOneCutoff E g μ hμ h hh φ hφ (fun x => χ x * η x)
        (fun a => (hχ a).mul (hη a)) (cutoff_mul_mem_Icc χ η hχb hηb)
        (realizeWeightedOneSection E g μ hμ h hh φ hφ U)
    rw [weightedOneCutoff_realize, weightedOneCutoff_realize, weightedOneCutoff_realize]
    congr 1
    apply Subtype.ext
    exact multiplyForm_real_mul E χ η U.1

theorem weightedOneCutoff_sq (χ : M.Carrier → ℝ) (hχ : SmoothFn χ)
    (hχb : ∀ x, χ x ∈ Set.Icc (0 : ℝ) 1)
    (W : WeightedOneHilbert E g μ hμ h hh φ hφ) :
    weightedOneCutoff E g μ hμ h hh φ hφ χ hχ hχb
      (weightedOneCutoff E g μ hμ h hh φ hφ χ hχ hχb W) =
      weightedOneCutoff E g μ hμ h hh φ hφ (fun x => χ x ^ 2)
        (fun a => (hχ a).pow 2) (cutoff_sq_mem_Icc χ hχb) W := by
  simpa only [pow_two] using weightedOneCutoff_mul E g μ hμ h hh φ hφ χ χ hχ hχ hχb hχb W

end Yau.LeafProofs.L14Aux
