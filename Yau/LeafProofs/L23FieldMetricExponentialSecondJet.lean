import Yau.LeafProofs.L23FieldMetricExponentialRadial

/-! The true radial second derivative of the actual exponential variation. -/
noncomputable section
open Filter
open scoped Topology ContDiff Manifold
namespace Yau.LeafProofs.L23Aux
open L12Aux L23LocalDistanceContract
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 800000

theorem fieldExp_chart_radial_secondJet
    (h : HermitianField M) (hh : MetricSmooth h) (x c : M.Carrier)
    (hc : x ∈ (chartAt (ComplexVector n) c).source)
    (V : TangentSpace 𝓘(ℝ, ComplexVector n) x) :
    HasDerivAt (deriv (fun r : ℝ => chartPt c (fieldExp h x (r • V))))
      (-chartChristoffelBilin h c (chartPt c x) (realTangentCoords c x V) (realTangentCoords c x V)) 0 := by
  obtain ⟨δ,hδ,Hgeo,Hphase⟩ := exists_radial_fieldExp_geodesic h hh x V
  have h0 : (0 : ℝ) ∈ Set.Ioo (-δ) δ := by constructor <;> linarith
  have hsource : fieldExp h x ((0 : ℝ) • V) ∈ (extChartAt (ComplexModel n) c).source := by
    rw [zero_smul,fieldExp_zero h hh]
    simpa only [extChartAt_source] using hc
  have H := (Hgeo.2 c 0 h0 hsource).snd
  change HasDerivAt (deriv (fun r : ℝ => chartPt c (fieldExp h x (r • V))))
    (chartGeodesicAcceleration h c
      (geoChartState (fun r => fieldExp h x (r • V)) c 0).1
      (geoChartState (fun r => fieldExp h x (r • V)) c 0).2) 0 at H
  simpa only [Hphase c hc,chartGeodesicAcceleration_eq] using H

theorem parallelExpVariation_chart_radial_secondJet
    (h : HermitianField M) (hh : MetricSmooth h) (γ : ℝ → M.Carrier)
    (P : (u : ℝ) → ComplexVector n →L[ℝ] TangentSpace 𝓘(ℝ, ComplexVector n) (γ u))
    (c : M.Carrier) (u : ℝ) (hc : γ u ∈ (chartAt (ComplexVector n) c).source)
    (w : ComplexVector n) :
    HasDerivAt (deriv (fun r : ℝ => chartPt c (parallelExpVariation h γ P u (r • w))))
      (-chartChristoffelBilin h c (chartPt c (γ u))
        (u • realTangentCoords c (γ u) (P u w)) (u • realTangentCoords c (γ u) (P u w))) 0 := by
  have H := fieldExp_chart_radial_secondJet h hh (γ u) c hc (u • P u w)
  convert! H using 1
  · ext r
    simp only [parallelExpVariation,map_smul,smul_smul,mul_comm]
  · simp only [map_smul]

end Yau.LeafProofs.L23Aux
