import Yau.Proofs.C05GradientFlowGeodesicFTC
import Yau.Proofs.C05GradientFlowIntegralRegularity
import Yau.LeafProofs.L12EndpointEnergyComposition

/-! Genuine endpoint energy variations and their gradient momenta. -/
noncomputable section
open Filter
open scoped Topology Manifold ContDiff
namespace Yau.Proofs.C05GradientFlowAux
open Yau Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5
set_option maxHeartbeats 1200000

theorem realChartMomentum_gradient (g : SmoothMetric M)
    (f : M.Carrier → ℝ) (hf : SmoothFn f) (c : M.Carrier)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)
    (hp : p.proj ∈ (chartAt (ComplexVector n) c).source) :
    realChartMomentum g c p (realGradInChart g.form f c (chartPt c p.proj)) =
      scalarVelocity f p := by
  have hz : chartPt c p.proj ∈ chartTarget c :=
    (extChartAt (ComplexModel n) c).map_source (by simpa only [extChartAt_source] using hp)
  unfold realChartMomentum
  have hsym (u v : ComplexVector n) :
      realMetricInChart g.form c (chartPt c p.proj) u v =
        realMetricInChart g.form c (chartPt c p.proj) v u := by
    simp only [realMetricInChart_apply]
    exact (underlyingRealRiemannianMetric g.form).symm _ _ _
  rw [hsym, realGradInChart_dual g.form f c _ hz]
  exact df_inChart_frame f hf c p.proj hp p.2

theorem endpointBranchEnergy_hasDerivAt
    (g : SmoothMetric M) (d : ℝ) (U : Set (M.Carrier × M.Carrier)) (hU : IsOpen U)
    (P : M.Carrier × M.Carrier → TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)
    (α β : ℝ → M.Carrier) (t : ℝ) (c e : M.Carrier)
    (v w : ComplexVector n) (ht : (α t, β t) ∈ U)
    (hc : α t ∈ (chartAt (ComplexVector n) c).source)
    (he : β t ∈ (chartAt (ComplexVector n) e).source) :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    ContMDiffOn (𝓘(ℝ, ComplexVector n).prod 𝓘(ℝ, ComplexVector n)) (realPhaseModel n) 1 P U →
    (∀ z ∈ U, (P z).proj = z.1 ∧ (realGeodesicFlow g (P z) d).proj = z.2) →
    ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 1 α t →
    ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 1 β t →
    HasDerivAt (fun s => chartPt c (α s)) v t →
    HasDerivAt (fun s => chartPt e (β s)) w t →
    HasDerivAt (fun s => realSegmentEnergy g d (P (α s, β s)))
      (-realChartMomentum g c (P (α t, β t)) v +
        realChartMomentum g e (realGeodesicFlow g (P (α t, β t)) d) w) t := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  intro hP hends hα hβ hcv hew
  have H := realSegmentEnergy_endpointComposition_hasFDerivAt g d U hU P
    (fun s => (α s, β s)) t c e ht hc he hP hends (hα.prodMk hβ)
  rw [(hcv.prodMk hew).hasFDerivAt.fderiv] at H
  convert H.hasDerivAt using 1 <;>
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coprod_apply,
      neg_apply, ContinuousLinearMap.toSpanSingleton_apply, one_smul]

end Yau.Proofs.C05GradientFlowAux
