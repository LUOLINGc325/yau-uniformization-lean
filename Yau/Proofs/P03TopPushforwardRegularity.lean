import Yau.LeafProofs.L14

open scoped Manifold Topology ContDiff
open Filter Bundle

noncomputable section

namespace Yau.NodeProofs.P03Aux

open Yau.BundleDbar Yau.LeafProofs.L14Aux

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

/-- A genuine local holomorphic coefficient, reconstructed in the actual
fibres, is holomorphic in every overlapping actual chart. -/
theorem topFormPushforward_coefficients_differentiableAt
    (hE : Holomorphic (r := r) E) (a : M.Carrier)
    (F : ComplexVector n → ComplexVector r)
    (hF : DifferentiableOn ℂ F (localDomain (r := r) E a))
    (b : M.Carrier) {z : ComplexVector n} (hz : z ∈ localDomain (r := r) E b)
    (ha : chartInv b z ∈ bundleChartSource (r := r) E a) :
    DifferentiableAt ℂ
      (fun w => coefficients (r := r) E (topFormPushforward (r := r) E a F) b w Fin.elim0) z := by
  let T : ComplexVector n → ComplexVector n := fun w => chartPt a (chartInv b w)
  have hT : ContDiffAt ℂ ∞ T z := Yau.LeafProofs.L18Aux.chartTransition_contDiffAt b a hz.1 ha.1
  have hTa : T z ∈ localDomain (r := r) E a := by
    refine ⟨(extChartAt (ComplexModel n) a).map_source ha.1, ?_⟩
    change chartInv a (chartPt a (chartInv b z)) ∈ (localTriv (r := r) E a).baseSet
    rw [Yau.LeafProofs.chartInv_chartPt_of_mem a _ (by simpa only [extChartAt_source] using ha.1)]
    exact ha.2
  have hFc : DifferentiableAt ℂ (fun w => F (T w)) z :=
    ((hF (T z) hTa).differentiableAt ((localDomain_isOpen E a).mem_nhds hTa)).comp z
      (hT.differentiableAt (by simp))
  have hA := (topBundleTransition_contDiffAt E hE a b z hz ha).differentiableAt (by simp)
  have he : (fun w => coefficients (r := r) E
      (topFormPushforward (r := r) E a F) b w Fin.elim0) =ᶠ[𝓝 z]
        (fun w => topBundleTransition (r := r) E a b w (F (T w))) := by
    have hci : ContinuousAt (chartInv b) z :=
      (continuousOn_extChartAt_symm (I := ComplexModel n) b z hz.1).continuousAt
        ((isOpen_extChartAt_target b).mem_nhds hz.1)
    have hna : ∀ᶠ w in 𝓝 z, chartInv b w ∈ bundleChartSource (r := r) E a :=
      hci ((bundleChartSource_isOpen (r := r) E a).mem_nhds ha)
    filter_upwards [(localDomain_isOpen E b).mem_nhds hz, hna] with w hw hwa
    exact topFormPushforward_coefficients_inChart E a b F w hw hwa
  exact (hA.clm_apply hFc).congr_of_eventuallyEq he

end Yau.NodeProofs.P03Aux
