import Yau.LeafProofs.L14ChartNorm

set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped Manifold Topology ContDiff
open MeasureTheory Bundle Filter Module

namespace Yau.LeafProofs.L14Aux
open BundleDbar

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

theorem bundle_chartPullbackZero_properties (a : M.Carrier) (η : M.Carrier → ℝ)
    (hη : SmoothFn η) (hcη : HasCompactSupport η)
    (hsη : tsupport η ⊆ bundleChartSource (r := r) E a) :
    ContDiff ℝ ∞ (L18Aux.chartPullbackZero a η) ∧ HasCompactSupport (L18Aux.chartPullbackZero a η) ∧
      tsupport (L18Aux.chartPullbackZero a η) ⊆ localDomain (r := r) E a := by
  have hηchart : tsupport η ⊆ (extChartAt (ComplexModel n) a).source := hsη.trans Set.inter_subset_left
  obtain ⟨hcψ, hψ, _⟩ := L18Aux.chartPullbackZero_smoothFn a hη hcη hηchart
  refine ⟨hψ, hcψ, ?_⟩
  intro z hz
  rcases L18Aux.chartPullbackZero_tsupport_subset a hcη hηchart hz with ⟨x, hx, rfl⟩
  refine ⟨(extChartAt (ComplexModel n) a).map_source (hsη hx).1, ?_⟩
  change chartInv a (chartPt a x) ∈ (localTriv (r := r) E a).baseSet
  rw [chartInv_chartPt_of_mem a x (by simpa only [extChartAt_source] using (hsη hx).1)]
  exact (hsη hx).2

variable (g : Yau.SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
  (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
  (hE : Holomorphic (r := r) E)

include hE in
/-- Local Friedrichs models reconstruct actual global weighted bundle sections
converging to a genuine compact scalar localization of the rough input. -/
theorem exists_compact_chart_input_graph_approx
    (U : WeightedOneSection E g μ hμ h hh φ hφ)
    (S : WeightedTopSection E g μ hμ h hh φ hφ)
    (hUS : (realizeWeightedOneSection E g μ hμ h hh φ hφ U,
      realizeWeightedTopSection E g μ hμ h hh φ hφ S) ∈
      (weightedMaximalDbar E g μ hμ h hh φ hφ).adjoint.graph)
    (f : NQForm E 2) (huf : WeakDbar (r := r) E U.1 f)
    (a : M.Carrier) (η : M.Carrier → ℝ) (hη : SmoothFn η)
    (hcη : HasCompactSupport η) (hsη : tsupport η ⊆ bundleChartSource (r := r) E a)
    (V : WeightedOneSection E g μ hμ h hh φ hφ)
    (hV : V.1 = multiplyForm E (fun x => (η x : ℂ)) U.1) :
    ∃ (K : Set (ComplexVector n)) (F : ℕ → ComplexVector n → Fin n → ComplexVector r),
      ∃ (hK : IsCompact K) (hKO : K ⊆ localDomain (r := r) E a)
        (hF : ∀ j, ContDiff ℝ ∞ (F j)) (hsF : ∀ j, tsupport (F j) ⊆ K),
      Tendsto (fun j => realizeWeightedOneSection E g μ hμ h hh φ hφ
        (weightedOneChartSection E g μ hμ h hh φ hφ hE a (F j) (hF j)
          (hK.of_isClosed_subset (isClosed_tsupport _) (hsF j)) ((hsF j).trans hKO)))
        atTop (𝓝 (realizeWeightedOneSection E g μ hμ h hh φ hφ V)) ∧
      ∀ row, (∀ j, MemLp (fun z => bundleModelSystemOutput E g.form h φ a (F j) z row -
        localizedBundleSystemOutput (r := r) E g.form h φ U.1 S.1 f a (L18Aux.chartPullbackZero a η) z row)
        2 (lebesgueC n)) ∧
        Tendsto (fun j => ∫ z, ‖bundleModelSystemOutput E g.form h φ a (F j) z row -
          localizedBundleSystemOutput (r := r) E g.form h φ U.1 S.1 f a (L18Aux.chartPullbackZero a η) z row‖ ^ 2
          ∂lebesgueC n) atTop (𝓝 0) := by
  classical
  let χ := L18Aux.chartPullbackZero a η
  obtain ⟨hχ, hcχ, hsχ⟩ := bundle_chartPullbackZero_properties E a η hη hcη hsη
  obtain ⟨L, F, hcL, hLO, hF, htF, htP⟩ :=
    exists_localized_bundle_model_graph_approx E g μ hμ h hh φ hφ hE U S hUS f huf a χ hχ hcχ hsχ
  let K := L ∪ tsupport χ
  have hK : IsCompact K := hcL.union hcχ
  have hKO : K ⊆ localDomain (r := r) E a := Set.union_subset hLO hsχ
  have hsF (j : ℕ) : tsupport (F j) ⊆ K := (hF j).2.trans Set.subset_union_left
  let G := compactOneChartCoefficients (r := r) E η U.1 a
  have hG : G = unflattenOneModel (localizedBundleSystemInput (r := r) E U.1 a χ) := by
    funext z i
    apply PiLp.ext
    intro α
    rfl
  have hsG : tsupport G ⊆ K := by
    rw [hG]
    exact (unflattenOneModel_tsupport_subset _ (isClosed_tsupport χ)
      (fun c => (localizedBundleSystemInput_properties E U.1 U.2.1 a χ hχ hcχ hsχ c).2)).trans Set.subset_union_right
  have hVpush : V.1 = oneFormPushforward (r := r) E a G :=
    hV.trans (multiplyForm_eq_oneFormPushforward E η U.1 a hsη)
  refine ⟨K, F, hK, hKO, fun j => (hF j).1, hsF, ?_, htP⟩
  apply weightedOneChartSection_tendsto_of_model_arrays E g μ hμ h hh φ hφ hE a K hK hKO
    F (fun j => (hF j).1) hsF G hsG V hVpush
  · exact fun j c => (htF c).1 j
  · exact fun c => (htF c).2

end Yau.LeafProofs.L14Aux
