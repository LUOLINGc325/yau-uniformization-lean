import Yau.LeafProofs.L14TopChartNorm

set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Manifold Topology ContDiff
open MeasureTheory Bundle Filter Module
namespace Yau.LeafProofs.L14Aux
open BundleDbar
variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)] [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]
theorem topTensorCoordinatesEquiv_at_chartPt (u : NQForm E 0) (a x : M.Carrier)
    (hx : x ∈ bundleChartSource (r := r) E a) :
    topTensorCoordinatesEquiv (r := r) E a x hx (u x) =
      coefficients (r := r) E u a (chartPt a x) Fin.elim0 := by
  classical
  have hz : chartPt a x ∈ localDomain (r := r) E a := by
    refine ⟨(extChartAt (ComplexModel n) a).map_source hx.1, ?_⟩
    change chartInv a (chartPt a x) ∈ (localTriv (r := r) E a).baseSet
    rw [chartInv_chartPt_of_mem a x (by simpa only [extChartAt_source] using hx.1)]
    exact hx.2
  let T : M.Carrier → ComplexVector r := fun y => if hy : y ∈ bundleChartSource (r := r) E a then
    topTensorCoordinatesEquiv (r := r) E a y hy (u y) else 0
  have hi : chartInv a (chartPt a x) = x := chartInv_chartPt_of_mem a x
    (by simpa only [extChartAt_source] using hx.1)
  have hxa : chartInv a (chartPt a x) ∈ bundleChartSource (r := r) E a :=
    ⟨(extChartAt (ComplexModel n) a).map_target hz.1, hz.2⟩
  calc
    _ = T x := by simp only [T, dif_pos hx]
    _ = T (chartInv a (chartPt a x)) := congrArg T hi.symm
    _ = _ := by simpa only [T, dif_pos hxa] using topTensorCoordinatesEquiv_form E u a (chartPt a x) hz

theorem topForm_eq_pushforward_of_chart_coefficients (u : NQForm E 0) (a : M.Carrier)
    (G : ComplexVector n → ComplexVector r)
    (hzero : ∀ x, x ∉ bundleChartSource (r := r) E a → u x = (0 : NQForm E 0) x)
    (hcoeff : ∀ z ∈ localDomain (r := r) E a, coefficients (r := r) E u a z Fin.elim0 = G z) :
    u = topFormPushforward (r := r) E a G := by
  classical
  funext x
  change u x = if hx : x ∈ bundleChartSource (r := r) E a then
    (topTensorCoordinatesEquiv (r := r) E a x hx).symm (G (chartPt a x)) else 0
  split_ifs with hx
  · apply (topTensorCoordinatesEquiv (r := r) E a x hx).injective
    rw [LinearEquiv.apply_symm_apply, topTensorCoordinatesEquiv_at_chartPt E u a x hx]
    apply hcoeff
    refine ⟨(extChartAt (ComplexModel n) a).map_source hx.1, ?_⟩
    change chartInv a (chartPt a x) ∈ (localTriv (r := r) E a).baseSet
    rw [chartInv_chartPt_of_mem a x (by simpa only [extChartAt_source] using hx.1)]
    exact hx.2
  · exact hzero x hx

variable (g : Yau.SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
  (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
  (hE : Holomorphic (r := r) E)
include hE in
theorem weightedTopChartSection_tendsto_of_model_arrays
    (a : M.Carrier) (K : Set (ComplexVector n)) (hK : IsCompact K) (hKO : K ⊆ localDomain (r := r) E a)
    (F : ℕ → ComplexVector n → ComplexVector r) (hF : ∀ j, ContDiff ℝ ∞ (F j))
    (hsF : ∀ j, tsupport (F j) ⊆ K)
    (G : ComplexVector n → ComplexVector r) (hsG : tsupport G ⊆ K)
    (V : WeightedTopSection E g μ hμ h hh φ hφ) (hV : V.1 = topFormPushforward (r := r) E a G)
    (he : ∀ j α, MemLp (fun z => F j z α - G z α) 2 (lebesgueC n))
    (ht : ∀ α, Tendsto (fun j => ∫ z, ‖F j z α - G z α‖ ^ 2 ∂lebesgueC n) atTop (𝓝 0)) :
    Tendsto (fun j => realizeWeightedTopSection E g μ hμ h hh φ hφ
      (weightedTopChartSection E g μ hμ h hh φ hφ hE a (F j) (hF j)
        (hK.of_isClosed_subset (isClosed_tsupport _) (hsF j)) ((hsF j).trans hKO)))
      atTop (𝓝 (realizeWeightedTopSection E g μ hμ h hh φ hφ V)) := by
  classical
  let U := fun j => weightedTopChartSection E g μ hμ h hh φ hφ hE a (F j) (hF j)
    (hK.of_isClosed_subset (isClosed_tsupport _) (hsF j)) ((hsF j).trans hKO)
  apply weightedTopSection_tendsto_of_compact_chart_errors E g μ hμ h hh φ hφ a K hK hKO U V
    (e := fun j z α => F j z α - G z α)
  · intro j x hx
    have hsub := WeightedTopSection.toForm_sub E g μ hμ h hh φ hφ (U j) V
    change (U j - V).1 = (U j).1 - V.1 at hsub
    rw [hsub, hV]
    have hU : (U j).1 = topFormPushforward (r := r) E a (F j) := rfl
    rw [hU]
    change (if h : x ∈ bundleChartSource (r := r) E a then
      (topTensorCoordinatesEquiv (r := r) E a x h).symm (F j (chartPt a x)) else 0) -
      (if h : x ∈ bundleChartSource (r := r) E a then
      (topTensorCoordinatesEquiv (r := r) E a x h).symm (G (chartPt a x)) else 0) = 0
    rw [dif_neg hx, dif_neg hx]
    apply Subtype.ext
    exact sub_self _
  · exact he
  · intro j α
    apply closure_minimal _ hK.isClosed
    intro z hz
    by_contra hn
    apply hz
    have hFz : F j z α = 0 := image_eq_zero_of_notMem_tsupport (f := fun w => F j w α)
      (fun hs => hn (hsF j (tsupport_comp_subset (g := fun V : ComplexVector r => V α) (by rfl) (F j) hs)))
    have hGz : G z α = 0 := image_eq_zero_of_notMem_tsupport (f := fun w => G w α)
      (fun hs => hn (hsG (tsupport_comp_subset (g := fun V : ComplexVector r => V α) (by rfl) G hs)))
    exact sub_eq_zero.mpr (hFz.trans hGz.symm)
  · intro j z hz α
    have hsub := WeightedTopSection.toForm_sub E g μ hμ h hh φ hφ (U j) V
    change (U j - V).1 = (U j).1 - V.1 at hsub
    rw [hsub, coefficients_sub, hV]
    change coefficients (r := r) E (topFormPushforward (r := r) E a (F j)) a z Fin.elim0 α -
      coefficients (r := r) E (topFormPushforward (r := r) E a G) a z Fin.elim0 α = _
    rw [topFormPushforward_coefficients E a (F j) z hz, topFormPushforward_coefficients E a G z hz]
  · exact ht
end Yau.LeafProofs.L14Aux
