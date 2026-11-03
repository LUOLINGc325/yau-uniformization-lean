import Yau.LeafProofs.L14CompactRieszPair
import Yau.LeafProofs.L14CompactDbar
import Yau.LeafProofs.L14RoughOnePairing

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
  (hE : Holomorphic (r := r) E)

include hE in
/-- The original Riesz pair annihilates the actual dbar of a computed compact two-form adjoint. -/
theorem compact_joint_riesz_pair_twoAdjoint_test
    (f : NQForm E 1) (hf : LocallyL2 (r := r) E f) (hclosed : WeaklyClosed (r := r) E f)
    (u : WeightedTopHilbert E g μ hμ h hh φ hφ)
    (w : WeightedTwoHilbert E g μ hμ h hh φ hφ)
    (hrep : ∀ t : CompactJointTriple E g μ hμ h hh φ hφ,
      IsCompactJointTriple E g μ hμ h hh φ hφ t →
      inner ℂ u (realizeWeightedTopSection E g μ hμ h hh φ hφ t.2.1) +
        inner ℂ w (realizeWeightedTwoSection E g μ hμ h hh φ hφ t.2.2) =
          weightedOneInner E g.form μ h φ f t.1.1)
    (η : NQForm E 2) (hη : SmoothForm (r := r) E η)
    (hcη : IsCompact (closure {x | η x ≠ (0 : NQForm E 2) x})) :
    ∃ (R : WeightedOneSection E g μ hμ h hh φ hφ)
      (D : WeightedTwoSection E g μ hμ h hh φ hφ),
      IsCompactJointTriple E g μ hμ h hh φ hφ (R,0,D) ∧
      MaximalDbarGraph (r := r) E g.form h μ φ R.1 D.1 ∧
      (∀ (v : NQForm E 1) (b : NQForm E 2), WeakDbar (r := r) E v b →
        (∫ x, weightedTwoPairing E g.form h φ b η x ∂μ) =
          weightedOneInner E g.form μ h φ v R.1) ∧
      inner ℂ w (realizeWeightedTwoSection E g μ hμ h hh φ hφ D) = 0 := by
  obtain ⟨R,hRs,hRc,hR0,hgreen,hann⟩ :=
    rough_smooth_compact_twoForm_has_co_closed_adjoint E g μ hμ h hh φ hφ hE η hη hcη
  obtain ⟨D,hDs,hDc,hRD,hgraph⟩ :=
    smooth_compact_oneForm_has_dbar E g μ hμ h hh φ hφ hE R.1 hRs hRc
  let DW : WeightedTwoSection E g μ hμ h hh φ hφ := ⟨D,hgraph.2.1⟩
  have ht : IsCompactJointTriple E g μ hμ h hh φ hφ (R,0,DW) := by
    refine ⟨hRs,hRc,smoothForm_zero E 0,compact_formSupport_zero E 0,hDs,hDc,hRD,?_⟩
    simpa only [realizeWeightedTopSection,UniformSpace.Completion.coe_zero] using hR0
  refine ⟨R,DW,ht,hgraph,hgreen,?_⟩
  have he := hrep (R,0,DW) ht
  have hz := hann f ⟨hf,hclosed.2⟩
  simpa only [realizeWeightedTopSection,UniformSpace.Completion.coe_zero,inner_zero_right,zero_add,hz] using he

include hE in
/-- The same annihilation for each explicit smooth compact skew chart model. -/
theorem compact_joint_riesz_pair_chartTwoAdjoint_test
    (f : NQForm E 1) (hf : LocallyL2 (r := r) E f) (hclosed : WeaklyClosed (r := r) E f)
    (u : WeightedTopHilbert E g μ hμ h hh φ hφ)
    (w : WeightedTwoHilbert E g μ hμ h hh φ hφ)
    (hrep : ∀ t : CompactJointTriple E g μ hμ h hh φ hφ,
      IsCompactJointTriple E g μ hμ h hh φ hφ t →
      inner ℂ u (realizeWeightedTopSection E g μ hμ h hh φ hφ t.2.1) +
        inner ℂ w (realizeWeightedTwoSection E g μ hμ h hh φ hφ t.2.2) =
          weightedOneInner E g.form μ h φ f t.1.1)
    (a : M.Carrier) (F : ComplexVector n → Fin n → Fin n → ComplexVector r)
    (hF : ContDiff ℝ ∞ F) (hcF : HasCompactSupport F)
    (hsF : tsupport F ⊆ localDomain (r := r) E a)
    (hskew : ∀ z i j, F z j i = -F z i j) :
    let R := weightedTwoDbarAdjointChartSection E g μ hμ h hh φ hφ hE a F hF hcF hsF
    ∃ D : WeightedTwoSection E g μ hμ h hh φ hφ,
      IsCompactJointTriple E g μ hμ h hh φ hφ (R,0,D) ∧
      MaximalDbarGraph (r := r) E g.form h μ φ R.1 D.1 ∧
      inner ℂ w (realizeWeightedTwoSection E g μ hμ h hh φ hφ D) = 0 := by
  let R := weightedTwoDbarAdjointChartSection E g μ hμ h hh φ hφ hE a F hF hcF hsF
  obtain ⟨hRs,hRc⟩ :=
    weightedTwoDbarAdjointChartSection_smooth_compact E g μ hμ h hh φ hφ hE a F hF hcF hsF
  have hgreen (v : NQForm E 1) (b : NQForm E 2) (hvb : WeakDbar (r := r) E v b) :
      (∫ x, weightedTwoPairing E g.form h φ b (twoFormPushforward E a F) x ∂μ) =
        weightedOneInner E g.form μ h φ v R.1 :=
    rough_weakDbar_weighted_chartTwo_adjoint_pairing E g μ hμ h hh φ hφ hE v b hvb
      a F hF hcF hsF hskew
  have hR0 := twoAdjoint_green_co_closed E g μ hμ h hh φ hφ hE (twoFormPushforward E a F) R
    (fun V b hVb => hgreen V.1 b hVb)
  obtain ⟨D,hDs,hDc,hRD,hgraph⟩ :=
    smooth_compact_oneForm_has_dbar E g μ hμ h hh φ hφ hE R.1 hRs hRc
  let DW : WeightedTwoSection E g μ hμ h hh φ hφ := ⟨D,hgraph.2.1⟩
  have ht : IsCompactJointTriple E g μ hμ h hh φ hφ (R,0,DW) := by
    refine ⟨hRs,hRc,smoothForm_zero E 0,compact_formSupport_zero E 0,hDs,hDc,hRD,?_⟩
    simpa only [realizeWeightedTopSection,UniformSpace.Completion.coe_zero] using hR0
  refine ⟨DW,ht,hgraph,?_⟩
  have he := hrep (R,0,DW) ht
  have hp := hgreen f 0 (weakDbar_zero_of_weaklyClosed E f ⟨hf,hclosed.2⟩)
  have hz : weightedOneInner E g.form μ h φ f R.1 = 0 := by
    simpa only [weightedTwoPairing_eq_zero_left,integral_zero] using hp.symm
  simpa only [realizeWeightedTopSection,UniformSpace.Completion.coe_zero,inner_zero_right,zero_add,hz] using he

end Yau.LeafProofs.L14Aux
