import Yau.Proofs.C04BoundedGeometryChartsNormalCenter
import Yau.Proofs.C04BoundedGeometryChartsNormalCoframe
import Yau.Proofs.C04BoundedGeometryChartsNijenhuisPullback

/-! Smoothness, square and integrability of the genuine pulled complex structure. -/
noncomputable section
open Filter
open scoped Topology Manifold ContDiff
namespace Yau.Proofs.C04ChartsAux
open Yau Yau.LeafProofs.L12Aux Yau.LeafProofs.L21Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 5

theorem realPullbackJ_intertwines (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p) (v w : ComplexVector n)
    (hi : (realMapDeriv (unitaryExponential g p U) v).IsInvertible) :
    realMapDeriv (unitaryExponential g p U) v
        (realPullbackJ (unitaryExponential g p U) v w) =
      realTangentJ (unitaryExponential g p U v) (realMapDeriv (unitaryExponential g p U) v w) :=
  hi.self_apply_inverse _

theorem unitaryExponential_chart_intertwines (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p) (c : M.Carrier) (v w : ComplexVector n)
    (hc : unitaryExponential g p U v ∈ (chartAt (ComplexVector n) c).source)
    (hi : (realMapDeriv (unitaryExponential g p U) v).IsInvertible) :
    fderiv ℝ (fun y => chartPt c (unitaryExponential g p U y)) v
        (realPullbackJ (unitaryExponential g p U) v w) =
      Complex.I • fderiv ℝ (fun y => chartPt c (unitaryExponential g p U y)) v w := by
  rw [← realMapDeriv_coordinates g p U c v hc]
  simp only [ContinuousLinearMap.comp_apply]
  rw [realPullbackJ_intertwines g p U v w hi, realTangentJ_eq_accepted,
    Yau.NodeProofs.P02Aux.realTangentCoords_realTangentJ c _ hc]

theorem realPullbackJ_square (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p) (v w : ComplexVector n)
    (hi : (realMapDeriv (unitaryExponential g p U) v).IsInvertible) :
    realPullbackJ (unitaryExponential g p U) v (realPullbackJ (unitaryExponential g p U) v w) = -w := by
  apply hi.injective
  rw [realPullbackJ_intertwines g p U v _ hi, realPullbackJ_intertwines g p U v w hi,
    realTangentJ_square, map_neg]

theorem realPullbackJ_smoothAt (g : SmoothMetric M) (hk : KahlerClosed g.form)
    (p : M.Carrier) (U : ComplexVector n ≃L[ℂ] TangentVector M p) (v : ComplexVector n)
    (hi : (realMapDeriv (unitaryExponential g p U) v).IsInvertible) :
    ContDiffAt ℝ ∞ (realPullbackJ (unitaryExponential g p U)) v := by
  have hA : ContDiffAt ℝ ∞ (radialCoframe g p U) v := (radialCoframe_smooth g p U).contDiffAt
  have hiA := (radialCoframe_invertible_iff_realMapDeriv g p U v).mpr hi
  have hAi := hiA.contDiffAt_map_inverse.comp v hA
  have heq : realPullbackJ (unitaryExponential g p U) = fun y =>
      (radialCoframe g p U y).inverse.comp ((stdComplex n).comp (radialCoframe g p U y)) := by
    funext y
    apply ContinuousLinearMap.ext
    intro w
    exact realPullbackJ_eq_radial_conjugation g hk p U y w
  rw [heq]
  exact hAi.clm_comp (contDiffAt_const.clm_comp hA)

theorem realPullbackJ_nijenhuis_zero (g : SmoothMetric M) (hk : KahlerClosed g.form)
    (p : M.Carrier) (U : ComplexVector n ≃L[ℂ] TangentVector M p) (v a b : ComplexVector n)
    (hi : (realMapDeriv (unitaryExponential g p U) v).IsInvertible) :
    Yau.LeafCandidates.nijenhuis (realPullbackJ (unitaryExponential g p U)) v a b = 0 := by
  let c := unitaryExponential g p U v
  have hc : unitaryExponential g p U v ∈ (chartAt (ComplexVector n) c).source := mem_chart_source _ _
  have hZ := unitaryExponential_chart_smoothAt g p U c v hc
  have hA := radialCoframe_smooth g p U
  have hclose : ∀ᶠ y in 𝓝 v, (radialCoframe g p U y).IsInvertible :=
    hA.continuous.continuousAt.eventually
      (((radialCoframe_invertible_iff_realMapDeriv g p U v).mpr hi).eventually_nhds)
  apply nijenhuis_zero_of_differential_intertwines
    (fun y => chartPt c (unitaryExponential g p U y))
    (realPullbackJ (unitaryExponential g p U)) v (hZ.of_le (by simp))
    ((realPullbackJ_smoothAt g hk p U v hi).differentiableAt (by simp)) _ _ a b
  · rw [← radialFrameCoordinates_comp_coframe g p U c v hc]
    exact ((radialFrameCoordinates_invertible g p U c v hc).comp
      ((radialCoframe_invertible_iff_realMapDeriv g p U v).mpr hi)).injective
  · filter_upwards [hclose,
      (unitaryExponential_smooth g p U).continuous.continuousAt.preimage_mem_nhds
        ((chartAt (ComplexVector n) c).open_source.mem_nhds hc)] with y hy hc'
    intro w
    exact unitaryExponential_chart_intertwines g p U c y w hc'
      ((radialCoframe_invertible_iff_realMapDeriv g p U y).mp hy)

end Yau.Proofs.C04ChartsAux
