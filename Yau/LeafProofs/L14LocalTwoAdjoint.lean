import Yau.LeafProofs.L14PairChartGraphs
import Yau.LeafProofs.L14LocalPairCore
import Yau.LeafProofs.L14TwoChartApprox

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
  (a : M.Carrier) (K : Set (ComplexVector n)) (hK : IsCompact K)
  (hKO : K ⊆ localDomain (r := r) E a)

theorem compactTwoHilbertField_cutoff_ae
    (χ : M.Carrier → ℝ) (hχ : SmoothFn χ) (hbound : ∀ x, χ x ∈ Set.Icc (0 : ℝ) 1)
    (W : WeightedTwoHilbert E g μ hμ h hh φ hφ) (p : TwoCoefficientIndex n r) :
    (fun z => compactTwoHilbertField E g μ hμ h hh φ hφ a K hK hKO
      (weightedTwoCutoff E g μ hμ h hh φ hφ χ hχ hbound W) z p) =ᵐ[lebesgueC n]
    (fun z => Complex.ofReal (L18Aux.chartPullbackZero a χ z)*compactTwoHilbertField E g μ hμ h hh φ hφ a K hK hKO W z p) := by
  have he := (ae_eq_restrict_iff_indicator_ae_eq hK.measurableSet).mp
    (weightedTwoHilbertLocalCoefficient_cutoff_ae E g μ hμ h hh φ hφ a K hK hKO p χ hχ hbound W)
  apply he.trans
  exact Eventually.of_forall fun z => by
    change K.indicator (fun z => (χ (chartInv a z) : ℂ)*weightedTwoHilbertLocalCoefficient E g μ hμ h hh φ hφ a K hK hKO p W z) z =
      Complex.ofReal (L18Aux.chartPullbackZero a χ z)*K.indicator (weightedTwoHilbertLocalCoefficient E g μ hμ h hh φ hφ a K hK hKO p W) z
    by_cases hz : z ∈ K
    · rw [Set.indicator_of_mem hz,Set.indicator_of_mem hz]
      simp only [L18Aux.chartPullbackZero,ite_eq_left (hKO hz).1]
    · rw [Set.indicator_of_notMem hz,Set.indicator_of_notMem hz,mul_zero]


include hh hφ in
theorem localizedPairSystemOutput_tsupport
    (f : NQForm E 1) (u : WeightedTopHilbert E g μ hμ h hh φ hφ)
    (w : WeightedTwoHilbert E g μ hμ h hh φ hφ) (χ : ComplexVector n → ℝ)
    (hsχ : tsupport χ ⊆ K) (row : Fin n × Fin r) :
    tsupport (fun z => localizedPairSystemOutput E g μ hμ h hh φ hφ a K hK hKO f u w χ z row) ⊆ K :=
  (localizedComplexSystemOutput_tsupport_subset realVec _ χ _ _ row).trans hsχ

variable (hE : Holomorphic (r := r) E)
include hE hK hKO in
theorem exists_local_weightedTwoAdjointGraph_cutoff
    (f : NQForm E 1) (hf : LocallyL2 (r := r) E f)
    (u : WeightedTopHilbert E g μ hμ h hh φ hφ) (w : WeightedTwoHilbert E g μ hμ h hh φ hφ)
    (hrep : ∀ t : CompactJointTriple E g μ hμ h hh φ hφ,
      IsCompactJointTriple E g μ hμ h hh φ hφ t →
      inner ℂ u (realizeWeightedTopSection E g μ hμ h hh φ hφ t.2.1) +
        inner ℂ w (realizeWeightedTwoSection E g μ hμ h hh φ hφ t.2.2) = weightedOneInner E g.form μ h φ f t.1.1)
    (χ : M.Carrier → ℝ) (hχ : SmoothFn χ) (hcχ : HasCompactSupport χ)
    (hbound : ∀ x, χ x ∈ Set.Icc (0 : ℝ) 1)
    (hsχ : tsupport χ ⊆ bundleChartSource (r := r) E a)
    (hsK : tsupport (L18Aux.chartPullbackZero a χ) ⊆ interior K) :
    ∃ b : WeightedOneHilbert E g μ hμ h hh φ hφ,
      (weightedTwoCutoff E g μ hμ h hh φ hφ χ hχ hbound w,b) ∈ weightedTwoAdjointGraph E g μ hμ h hh φ hφ := by
  classical
  let ψ := L18Aux.chartPullbackZero a χ
  obtain ⟨hψ,hcψ,_⟩ := bundle_chartPullbackZero_properties E a χ hχ hcχ hsχ
  obtain ⟨L,F,hL,hLK,hF,hinput,houtput⟩ := exists_localized_joint_pair_model_graph_approx E g μ hμ h hh φ hφ hE a K hK hKO f hf u w hrep ψ hψ hcψ hsK
  have hFs (m : ℕ) (c : PairSystemInputIndex n r) : tsupport (fun z => F m z c) ⊆ K :=
    (hF m c).2.trans (hLK.trans interior_subset)
  have hFm (m : ℕ) : ContDiff ℝ ∞ (pairModelTwo (F m)) :=
    (pairModels_properties (F m) (fun c => (hF m c).1) hK.isClosed (hFs m)).2.1
  have hsFm (m : ℕ) : tsupport (pairModelTwo (F m)) ⊆ K :=
    (pairModels_properties (F m) (fun c => (hF m c).1) hK.isClosed (hFs m)).2.2.2
  have heq (p : TwoCoefficientIndex n r) :
      (fun z => compactTwoHilbertField E g μ hμ h hh φ hφ a K hK hKO
        (weightedTwoCutoff E g μ hμ h hh φ hφ χ hχ hbound w) z p) =ᵐ[lebesgueC n]
      (fun z => localizedPairSystemInput E g μ hμ h hh φ hφ a K hK hKO u w ψ z (.inr p)) :=
    compactTwoHilbertField_cutoff_ae E g μ hμ h hh φ hφ a K hK hKO χ hχ hbound w p
  have he (m : ℕ) (p : TwoCoefficientIndex n r) : MemLp
      (fun z => pairModelTwo (F m) z p.1.2 p.2 p.1.1-compactTwoHilbertField E g μ hμ h hh φ hφ a K hK hKO
        (weightedTwoCutoff E g μ hμ h hh φ hφ χ hχ hbound w) z p) 2 (lebesgueC n) := by
    exact (hinput (.inr p)).1 m |>.ae_eq ((heq p).mono fun z hz => by
      dsimp only at hz ⊢
      change F m z (.inr p)-_ = F m z (.inr p)-_
      rw [hz])
  have ht (p : TwoCoefficientIndex n r) : Tendsto (fun m => ∫ z,
      ‖pairModelTwo (F m) z p.1.2 p.2 p.1.1-compactTwoHilbertField E g μ hμ h hh φ hφ a K hK hKO
        (weightedTwoCutoff E g μ hμ h hh φ hφ χ hχ hbound w) z p‖^2 ∂lebesgueC n) atTop (𝓝 0) := by
    convert (hinput (.inr p)).2 using 1
    funext m
    apply integral_congr_ae
    filter_upwards [heq p] with z hz
    rw [hz]
    rfl
  have hW := weightedTwoAlternatingChartSection_tendsto_cutoff_of_model_errors E g μ hμ h hh φ hφ hE a K hK hKO
    χ hχ hbound hsχ (hsK.trans interior_subset) w (fun m => pairModelTwo (F m)) hFm hsFm he ht
  obtain ⟨b,hb,hgraph⟩ := pairChartAdjoint_limit_of_graph_errors E g μ hμ h hh φ hφ hE a K hK hKO F
    (fun m c => (hF m c).1) hFs (localizedPairSystemOutput E g μ hμ h hh φ hφ a K hK hKO f u w ψ)
    (localizedPairSystemOutput_tsupport E g μ hμ h hh φ hφ a K hK hKO f u w ψ (hsK.trans interior_subset))
    (fun m row => (houtput row).1 m) (fun row => (houtput row).2)
    (weightedTwoCutoff E g μ hμ h hh φ hφ χ hχ hbound w) hW
  exact ⟨b,hgraph⟩


include hE in
theorem exists_chart_weightedTwoAdjointGraph_cutoff
    (f : NQForm E 1) (hf : LocallyL2 (r := r) E f)
    (u : WeightedTopHilbert E g μ hμ h hh φ hφ) (w : WeightedTwoHilbert E g μ hμ h hh φ hφ)
    (hrep : ∀ t : CompactJointTriple E g μ hμ h hh φ hφ,
      IsCompactJointTriple E g μ hμ h hh φ hφ t →
      inner ℂ u (realizeWeightedTopSection E g μ hμ h hh φ hφ t.2.1) +
        inner ℂ w (realizeWeightedTwoSection E g μ hμ h hh φ hφ t.2.2) = weightedOneInner E g.form μ h φ f t.1.1)
    (χ : M.Carrier → ℝ) (hχ : SmoothFn χ) (hcχ : HasCompactSupport χ)
    (hbound : ∀ x, χ x ∈ Set.Icc (0 : ℝ) 1)
    (hsχ : tsupport χ ⊆ bundleChartSource (r := r) E a) :
    ∃ b : WeightedOneHilbert E g μ hμ h hh φ hφ,
      (weightedTwoCutoff E g μ hμ h hh φ hφ χ hχ hbound w,b) ∈ weightedTwoAdjointGraph E g μ hμ h hh φ hφ := by
  obtain ⟨_,hcψ,hsψ⟩ := bundle_chartPullbackZero_properties E a χ hχ hcχ hsχ
  obtain ⟨Ω,hΩ,hψΩ,hΩO,hcΩ⟩ := exists_open_between_and_isCompact_closure hcψ (localDomain_isOpen E a) hsψ
  exact exists_local_weightedTwoAdjointGraph_cutoff E g μ hμ h hh φ hφ a (closure Ω) hcΩ hΩO hE f hf u w hrep χ hχ hcχ hbound hsχ
    (hψΩ.trans hΩ.subset_interior_closure)

end Yau.LeafProofs.L14Aux
