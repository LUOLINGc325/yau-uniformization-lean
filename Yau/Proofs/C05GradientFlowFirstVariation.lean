import Yau.Proofs.C05GradientFlowBrokenEndpointSupport

/-! Right upper first variation of distance, including cut points. -/
noncomputable section
open Filter
open scoped Topology Manifold ContDiff
namespace Yau.Proofs.C05GradientFlowAux
open Yau Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

theorem endpoint_distance_upperRightSlopeLE (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)
    (α β : ℝ → M.Carrier) (t : ℝ) (v w : ComplexVector n)
    (hα0 : α t = p.proj) (hβ0 : β t = (realGeodesicFlow g p 1).proj)
    (hpos : 0 < inducedDistance g.form (α t) (β t))
    (hmin : realTangentEnergy g.form p = inducedDistance g.form (α t) (β t) ^ 2) :
    letI := manifold_realSmooth M
    ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 1 α t →
    ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 1 β t →
    HasDerivAt (fun s => chartPt p.proj (α s)) v t →
    HasDerivAt (fun s => chartPt (realGeodesicFlow g p 1).proj (β s)) w t →
    UpperRightSlopeLE (fun s => inducedDistance g.form (α s) (β s)) t
      ((-realChartMomentum g p.proj p v +
        realChartMomentum g (realGeodesicFlow g p 1).proj (realGeodesicFlow g p 1) w) /
          inducedDistance g.form (α t) (β t)) := by
  letI := manifold_realSmooth M
  intro hα hβ hv hw
  obtain ⟨E, hE, hder, hbound⟩ :=
    exists_broken_endpoint_energy_support g p α β t v w hα0 hβ0 hα hβ hv hw
  exact upperRightSlopeLE_of_energy_support hpos rfl (by rw [hE, hmin])
    (hbound.filter_mono nhdsWithin_le_nhds) hder

end Yau.Proofs.C05GradientFlowAux
