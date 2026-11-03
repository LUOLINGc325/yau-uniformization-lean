import Yau.LeafProofs.L14LocalTwoAdjointCore
import Yau.LeafProofs.L14TwoGraphTests
import Yau.LeafProofs.L14CutoffPlateau

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

/-- The actual smooth exterior derivative has a unique two-form representative. -/
theorem smoothDbarRepresents_two_unique (u : NQForm E 1) (D F : NQForm E 2)
    (hD : SmoothDbarRepresents (r := r) E u D)
    (hF : SmoothDbarRepresents (r := r) E u F) : D = F := by
  funext x
  have hx : x ∈ bundleChartSource (r := r) E x :=
    ⟨mem_extChartAt_source x, FiberBundle.mem_baseSet_trivializationAt' x⟩
  have hz : chartPt x x ∈ localDomain (r := r) E x := by
    refine ⟨mem_extChartAt_target x, ?_⟩
    change chartInv x (chartPt x x) ∈ (localTriv (r := r) E x).baseSet
    rw [chartInv_chartPt_of_mem x x (mem_chart_source _ _)]
    exact hx.2
  apply twoTensorCoordinates_injective E x x hx
  ext p
  rcases p with ⟨⟨α,i⟩,j⟩
  rw [twoTensorCoordinates_at_chartPt E D x x hx i j α,
    twoTensorCoordinates_at_chartPt E F x x hx i j α, hD x _ hz, hF x _ hz]

variable (g : Yau.SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
  (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
  (hE : Holomorphic (r := r) E)

include hE in
/-- On a plateau, the localized adjoint is orthogonal to every computed compact chart adjoint. -/
theorem compact_joint_riesz_pair_chartTwoAdjoint_plateau_orthogonal
    (f : NQForm E 1) (hf : LocallyL2 (r := r) E f) (hclosed : WeaklyClosed (r := r) E f)
    (u : WeightedTopHilbert E g μ hμ h hh φ hφ)
    (w : WeightedTwoHilbert E g μ hμ h hh φ hφ)
    (hrep : ∀ t : CompactJointTriple E g μ hμ h hh φ hφ,
      IsCompactJointTriple E g μ hμ h hh φ hφ t →
      inner ℂ u (realizeWeightedTopSection E g μ hμ h hh φ hφ t.2.1) +
        inner ℂ w (realizeWeightedTwoSection E g μ hμ h hh φ hφ t.2.2) =
          weightedOneInner E g.form μ h φ f t.1.1)
    (θ : M.Carrier → ℝ) (hθ : SmoothFn θ) (hθb : ∀ x, θ x ∈ Set.Icc (0 : ℝ) 1)
    (bθ : WeightedOneHilbert E g μ hμ h hh φ hφ)
    (hGθ : (weightedTwoCutoff E g μ hμ h hh φ hφ θ hθ hθb w,bθ) ∈
      weightedTwoAdjointGraph E g μ hμ h hh φ hφ)
    (a : M.Carrier) (K : Set (ComplexVector n))
    (hθK : ∀ z ∈ K, θ (chartInv a z) = 1)
    (F : ComplexVector n → Fin n → Fin n → ComplexVector r)
    (hF : ContDiff ℝ ∞ F) (hcF : HasCompactSupport F)
    (hsF : tsupport F ⊆ localDomain (r := r) E a) (hFK : tsupport F ⊆ K)
    (hskew : ∀ z i j, F z j i = -F z i j) :
    inner ℂ bθ (realizeWeightedOneSection E g μ hμ h hh φ hφ
      (weightedTwoDbarAdjointChartSection E g μ hμ h hh φ hφ hE a F hF hcF hsF)) = 0 := by
  classical
  let R := weightedTwoDbarAdjointChartSection E g μ hμ h hh φ hφ hE a F hF hcF hsF
  obtain ⟨D,ht,hRD,hann⟩ := compact_joint_riesz_pair_chartTwoAdjoint_test
    E g μ hμ h hh φ hφ hE f hf hclosed u w hrep a F hF hcF hsF hskew
  let Q := chartTwoDbarAdjoint E g.form h φ a F
  have hQ : ContDiff ℝ ∞ Q := chartTwoDbarAdjoint_contDiff E g h hh φ hφ a F hF hsF
  have hsQ : tsupport Q ⊆ tsupport F := tsupport_chartTwoDbarAdjoint_subset E g.form h φ a F
  have hcQ : HasCompactSupport Q := hcF.of_isClosed_subset (isClosed_tsupport _) hsQ
  have hQO : tsupport Q ⊆ localDomain (r := r) E a := hsQ.trans hsF
  have hD : D.1 = twoFormPushforward E a (modelOneDbar Q) :=
    smoothDbarRepresents_two_unique E R.1 D.1 _ ht.2.2.2.2.2.2.1
      (oneFormPushforward_representsDbar E hE a Q hQ hcQ hQO)
  have hcDQ : HasCompactSupport (modelOneDbar Q) :=
    hcQ.of_isClosed_subset (isClosed_tsupport _) (tsupport_modelOneDbar_subset Q)
  have hsDQ : tsupport (modelOneDbar Q) ⊆ localDomain (r := r) E a :=
    (tsupport_modelOneDbar_subset Q).trans hQO
  have hplateau (x : M.Carrier) (hx : D.1 x ≠ (0 : NQForm E 2) x) : θ x = 1 := by
    rw [hD] at hx
    obtain ⟨z,hz,rfl⟩ := twoFormPushforward_support E a (modelOneDbar Q) hcDQ hsDQ (subset_closure hx)
    exact hθK z (hFK (hsQ (tsupport_modelOneDbar_subset Q hz)))
  have hfix := weightedTwoCutoff_realize_eq_of_one E g μ hμ h hh φ hφ θ hθ hθb D hplateau
  have he := hGθ R D hRD.2.2
  change inner ℂ bθ (realizeWeightedOneSection E g μ hμ h hh φ hφ R) = 0
  rw [← inner_conj_symm bθ _, ← he, inner_conj_symm,
    weightedTwoCutoff_inner, hfix, hann]

include hE in
/-- The genuine local adjoint core preserves orthogonality to an enclosing cutoff adjoint. -/
theorem exists_local_weightedTwoAdjointGraph_orthogonal
    (f : NQForm E 1) (hf : LocallyL2 (r := r) E f) (hclosed : WeaklyClosed (r := r) E f)
    (u : WeightedTopHilbert E g μ hμ h hh φ hφ)
    (w : WeightedTwoHilbert E g μ hμ h hh φ hφ)
    (hrep : ∀ t : CompactJointTriple E g μ hμ h hh φ hφ,
      IsCompactJointTriple E g μ hμ h hh φ hφ t →
      inner ℂ u (realizeWeightedTopSection E g μ hμ h hh φ hφ t.2.1) +
        inner ℂ w (realizeWeightedTwoSection E g μ hμ h hh φ hφ t.2.2) =
          weightedOneInner E g.form μ h φ f t.1.1)
    (θ : M.Carrier → ℝ) (hθ : SmoothFn θ) (hθb : ∀ x, θ x ∈ Set.Icc (0 : ℝ) 1)
    (bθ : WeightedOneHilbert E g μ hμ h hh φ hφ)
    (hGθ : (weightedTwoCutoff E g μ hμ h hh φ hφ θ hθ hθb w,bθ) ∈
      weightedTwoAdjointGraph E g μ hμ h hh φ hφ)
    (a : M.Carrier) (K : Set (ComplexVector n)) (hK : IsCompact K)
    (hKO : K ⊆ localDomain (r := r) E a)
    (χ : M.Carrier → ℝ) (hχ : SmoothFn χ) (hcχ : HasCompactSupport χ)
    (hχb : ∀ x, χ x ∈ Set.Icc (0 : ℝ) 1)
    (hsχ : tsupport χ ⊆ bundleChartSource (r := r) E a)
    (hsK : tsupport (L18Aux.chartPullbackZero a χ) ⊆ interior K)
    (hθK : ∀ z ∈ K, θ (chartInv a z) = 1) :
    ∃ b : WeightedOneHilbert E g μ hμ h hh φ hφ,
      (weightedTwoCutoff E g μ hμ h hh φ hφ χ hχ hχb w,b) ∈
        weightedTwoAdjointGraph E g μ hμ h hh φ hφ ∧ inner ℂ bθ b = 0 := by
  classical
  obtain ⟨L,F,hL,hLK,hF,hsF,b,_hW,hb,hG⟩ :=
    exists_local_weightedTwoAdjointGraph_core E g μ hμ h hh φ hφ a K hK hKO hE
      f hf u w hrep χ hχ hcχ hχb hsχ hsK
  refine ⟨b,hG,?_⟩
  have horth (m : ℕ) : inner ℂ bθ (realizeWeightedOneSection E g μ hμ h hh φ hφ
      (pairChartAdjointSection E g μ hμ h hh φ hφ hE a L hL
        (hLK.trans (interior_subset.trans hKO)) (F m) (hF m) (hsF m))) = 0 := by
    let hp := pairModels_properties (F m) (hF m) hL.isClosed (hsF m)
    let hAlt := alternatingTwoModel_properties (pairModelTwo (F m)) hp.2.1
      (hL.of_isClosed_subset (isClosed_tsupport _) hp.2.2.2)
    exact compact_joint_riesz_pair_chartTwoAdjoint_plateau_orthogonal
      E g μ hμ h hh φ hφ hE f hf hclosed u w hrep θ hθ hθb bθ hGθ a K hθK
      (alternatingTwoModel (pairModelTwo (F m))) hAlt.1 hAlt.2.1
      (hAlt.2.2.trans (hp.2.2.2.trans (hLK.trans (interior_subset.trans hKO))))
      (hAlt.2.2.trans (hp.2.2.2.trans (hLK.trans interior_subset)))
      (alternatingTwoModel_skew _)
  have ht : Tendsto (fun m => inner ℂ bθ (realizeWeightedOneSection E g μ hμ h hh φ hφ
      (pairChartAdjointSection E g μ hμ h hh φ hφ hE a L hL
        (hLK.trans (interior_subset.trans hKO)) (F m) (hF m) (hsF m))))
      atTop (𝓝 (inner ℂ bθ b)) := tendsto_const_nhds.inner hb
  have hz : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 (inner ℂ bθ b)) := by
    simpa only [horth] using ht
  exact (tendsto_nhds_unique tendsto_const_nhds hz).symm

end Yau.LeafProofs.L14Aux
