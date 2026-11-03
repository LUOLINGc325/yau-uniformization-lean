import Yau.LeafProofs.L14

open scoped Manifold Topology ContDiff
open MeasureTheory Bundle

noncomputable section

namespace Yau.NodeProofs.P03Aux

open Yau.BundleDbar Yau.LeafProofs.L14Aux

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

theorem chartPt_mem_localDomain (a x : M.Carrier)
    (hx : x ∈ bundleChartSource (r := r) E a) :
    chartPt a x ∈ localDomain (r := r) E a := by
  refine ⟨(extChartAt (ComplexModel n) a).map_source hx.1, ?_⟩
  change chartInv a (chartPt a x) ∈ (localTriv (r := r) E a).baseSet
  rw [Yau.LeafProofs.chartInv_chartPt_of_mem a _ (by simpa only [extChartAt_source] using hx.1)]
  exact hx.2

theorem topTensorCoordinatesEquiv_at_chartPt (u : NQForm E 0) (a x : M.Carrier)
    (hx : x ∈ bundleChartSource (r := r) E a) :
    topTensorCoordinatesEquiv (r := r) E a x hx (u x) =
      coefficients (r := r) E u a (chartPt a x) Fin.elim0 := by
  have hi := Yau.LeafProofs.chartInv_chartPt_of_mem a x
    (by simpa only [extChartAt_source] using hx.1)
  calc
    _ = (localTriv (r := r) E a).continuousLinearMapAt ℂ x (topFormValue E u a x) :=
      (topTensorCoordinatesEquiv_apply E a x hx (u x)).trans
        (congrArg ((localTriv (r := r) E a).continuousLinearMapAt ℂ x)
          (topTensorValueEquiv_form E u a x hx.1))
    _ = _ := by
      ext α : 1
      have hc := coefficients_topFormValue E u a (chartPt a x) α
      rw [hi] at hc
      exact hc.symm

/-- An AE coefficient representative gives the same intrinsic top tensor
almost everywhere for the original geometric volume, on the actual chart. -/
theorem topFormPushforward_ae_eq_local (g : HermitianField M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g μ) (u : NQForm E 0) (a : M.Carrier)
    (F : ComplexVector n → ComplexVector r)
    (hF : (fun z => coefficients (r := r) E u a z Fin.elim0)
      =ᵐ[(lebesgueC n).restrict (localDomain (r := r) E a)] F) :
    ∀ᵐ x ∂μ.restrict (bundleChartSource (r := r) E a),
      topFormPushforward (r := r) E a F x = u x := by
  have ht := (chartPtExtension_quasiMeasurePreserving (r := r) E g μ hμ a).ae hF
  filter_upwards [ht, ae_restrict_mem (bundleChartSource_isOpen (r := r) E a).measurableSet]
    with x hx hxdom
  have hxF : coefficients (r := r) E u a (chartPt a x) Fin.elim0 = F (chartPt a x) := by
    simpa only [chartPtExtension, if_pos hxdom.1] using hx
  apply (topTensorCoordinatesEquiv (r := r) E a x hxdom).injective
  rw [topTensorCoordinatesEquiv_at_chartPt E _ a x hxdom,
    topTensorCoordinatesEquiv_at_chartPt E _ a x hxdom,
    topFormPushforward_coefficients E a F _ (chartPt_mem_localDomain E a x hxdom), hxF]

end Yau.NodeProofs.P03Aux
