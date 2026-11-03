import Yau.LeafProofs.L14BundleFriedrichsModels
import Yau.LeafProofs.L14ModelL2

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

variable (g : Yau.SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
  (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
  (hE : Holomorphic (r := r) E)

include hE in
/-- Actual chart-supported bundle sections inherit strong weighted Hilbert
convergence from the ordinary L² convergence of their model coefficients. -/
theorem weightedOneChartSection_tendsto_of_model_arrays
    (a : M.Carrier) (K : Set (ComplexVector n)) (hK : IsCompact K)
    (hKO : K ⊆ localDomain (r := r) E a)
    (F : ℕ → ComplexVector n → Fin n → ComplexVector r)
    (hF : ∀ j, ContDiff ℝ ∞ (F j)) (hsF : ∀ j, tsupport (F j) ⊆ K)
    (G : ComplexVector n → Fin n → ComplexVector r) (hsG : tsupport G ⊆ K)
    (V : WeightedOneSection E g μ hμ h hh φ hφ)
    (hV : V.1 = oneFormPushforward (r := r) E a G)
    (he : ∀ j (c : Fin n × Fin r), MemLp (fun z => F j z c.1 c.2 - G z c.1 c.2) 2 (lebesgueC n))
    (ht : ∀ c : Fin n × Fin r, Tendsto
      (fun j => ∫ z, ‖F j z c.1 c.2 - G z c.1 c.2‖ ^ 2 ∂lebesgueC n) atTop (𝓝 0)) :
    Tendsto (fun j => realizeWeightedOneSection E g μ hμ h hh φ hφ
      (weightedOneChartSection E g μ hμ h hh φ hφ hE a (F j) (hF j)
        (hK.of_isClosed_subset (isClosed_tsupport _) (hsF j)) ((hsF j).trans hKO)))
      atTop (𝓝 (realizeWeightedOneSection E g μ hμ h hh φ hφ V)) := by
  classical
  let U := fun j => weightedOneChartSection E g μ hμ h hh φ hφ hE a (F j) (hF j)
    (hK.of_isClosed_subset (isClosed_tsupport _) (hsF j)) ((hsF j).trans hKO)
  apply weightedOneSection_tendsto_of_compact_chart_errors E g μ hμ h hh φ hφ a K hK hKO U V
    (e := fun j z c => F j z c.1 c.2 - G z c.1 c.2)
  · intro j x hx
    have hsub := WeightedOneSection.toForm_sub E g μ hμ h hh φ hφ (U j) V
    change (U j - V).1 = (U j).1 - V.1 at hsub
    rw [hsub, hV]
    have hU : (U j).1 = oneFormPushforward (r := r) E a (F j) := rfl
    rw [hU]
    change (if h : x ∈ bundleChartSource (r := r) E a then
      oneTensorFromCoefficients (r := r) E a x h (F j (chartPt a x)) else 0) -
      (if h : x ∈ bundleChartSource (r := r) E a then
      oneTensorFromCoefficients (r := r) E a x h (G (chartPt a x)) else 0) = 0
    rw [dif_neg hx, dif_neg hx]
    apply Subtype.ext
    exact sub_self _
  · exact he
  · intro j c
    apply closure_minimal _ hK.isClosed
    intro z hz
    by_contra hn
    apply hz
    have hFz : F j z c.1 c.2 = 0 := image_eq_zero_of_notMem_tsupport
      (f := fun w => F j w c.1 c.2) (fun hs => hn ((hsF j)
        (tsupport_comp_subset (g := fun V : Fin n → ComplexVector r => V c.1 c.2) (by rfl) (F j) hs)))
    have hGz : G z c.1 c.2 = 0 := image_eq_zero_of_notMem_tsupport
      (f := fun w => G w c.1 c.2) (fun hs => hn (hsG
        (tsupport_comp_subset (g := fun V : Fin n → ComplexVector r => V c.1 c.2) (by rfl) G hs)))
    exact sub_eq_zero.mpr (hFz.trans hGz.symm)
  · intro j z hz c
    have hsub := WeightedOneSection.toForm_sub E g μ hμ h hh φ hφ (U j) V
    change (U j - V).1 = (U j).1 - V.1 at hsub
    rw [hsub, coefficients_sub, hV]
    change coefficients (r := r) E (oneFormPushforward (r := r) E a (F j)) a z (fun _ => c.1) c.2 -
      coefficients (r := r) E (oneFormPushforward (r := r) E a G) a z (fun _ => c.1) c.2 = _
    rw [oneFormPushforward_coefficients E a (F j) z hz c.1 c.2,
      oneFormPushforward_coefficients E a G z hz c.1 c.2]
  · exact ht

end Yau.LeafProofs.L14Aux
