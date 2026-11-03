import Yau.LeafProofs.L14TwoGraphCutoff
import Yau.LeafProofs.L14WeakCutoffProduct

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


theorem weightedTwoAdjointGraph_cutoff
    (χ : M.Carrier → ℝ) (hχ : SmoothFn χ) (hbound : ∀ x,χ x ∈ Set.Icc (0 : ℝ) 1)
    (C : ℝ) (hC : 0 ≤ C) (hgrad : ∀ x,gradNormSq g.form χ x ≤ C)
    (W : WeightedTwoHilbert E g μ hμ h hh φ hφ) (R : WeightedOneHilbert E g μ hμ h hh φ hφ)
    (hWR : (W,R) ∈ weightedTwoAdjointGraph E g μ hμ h hh φ hφ) :
    (weightedTwoCutoff E g μ hμ h hh φ hφ χ hχ hbound W,
      weightedOneCutoff E g μ hμ h hh φ hφ χ hχ hbound R-
        weightedTwoHilbertGradientContraction E g μ hμ h hh φ hφ χ hχ C hC hgrad W) ∈
      weightedTwoAdjointGraph E g μ hμ h hh φ hφ := by
  intro U D hUD
  let Uχ := weightedOneCutoffSection E g μ hμ h hh φ hφ χ hχ hbound U
  let Dχ := weightedTwoCutoffSection E g μ hμ h hh φ hφ χ hχ hbound D
  let V := weightedGradientWedgeSection E g μ hμ h hh φ hφ χ hχ C hC hgrad U
  have he := hWR Uχ (Dχ+V) (weakDbar_one_multiply_real E χ hχ U.1 D.1 hUD)
  have hreal : realizeWeightedTwoSection E g μ hμ h hh φ hφ (Dχ+V) =
      realizeWeightedTwoSection E g μ hμ h hh φ hφ Dχ+realizeWeightedTwoSection E g μ hμ h hh φ hφ V :=
    UniformSpace.Completion.coe_add _ _
  rw [hreal,inner_add_left] at he
  change inner ℂ (realizeWeightedTwoSection E g μ hμ h hh φ hφ Dχ) W+
    inner ℂ (realizeWeightedTwoSection E g μ hμ h hh φ hφ (weightedGradientWedgeSection E g μ hμ h hh φ hφ χ hχ C hC hgrad U)) W =
      inner ℂ (realizeWeightedOneSection E g μ hμ h hh φ hφ Uχ) R at he
  rw [weightedGradientWedge_inner] at he
  change inner ℂ (realizeWeightedTwoSection E g μ hμ h hh φ hφ (weightedTwoCutoffSection E g μ hμ h hh φ hφ χ hχ hbound D)) W+_ =
    inner ℂ (realizeWeightedOneSection E g μ hμ h hh φ hφ (weightedOneCutoffSection E g μ hμ h hh φ hφ χ hχ hbound U)) R at he
  rw [← weightedTwoCutoff_realize,← weightedOneCutoff_realize,weightedTwoCutoff_inner,weightedOneCutoff_inner] at he
  rw [inner_sub_right]
  exact eq_sub_iff_add_eq.mpr he

end Yau.LeafProofs.L14Aux
