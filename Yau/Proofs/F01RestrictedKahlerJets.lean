import Yau.Proofs.F01AmbientOpenChart
import Yau.Proofs.F01KahlerChartJets

/-! The actual restricted background has Kähler jet symmetry in every
holomorphic chart of the component; no complete SmoothMetric is fabricated. -/
noncomputable section
open Set Filter TopologicalSpace
open scoped Manifold Topology Matrix
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs.L17Aux
variable {n : ℕ} (M : ComplexManifold n) (S : Opens M.Carrier)
  (hS : IsConnected (S : Set M.Carrier))

theorem restricted_metric_pullback_wirt_symm (g : SmoothMetric M)
    (e : OpenPartialHomeomorph (ComplexVector n) (openConnectedManifold M S hS).Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    {z : ComplexVector n} (hz : z ∈ e.source) (i j k : Fin n) :
    wirt (fun w => pullbackMatrix (openRestrictedField M S hS g.form) e w i j) z (stdVec k) =
      wirt (fun w => pullbackMatrix (openRestrictedField M S hS g.form) e w i k) z (stdVec j) := by
  have hgerm (p q : Fin n) :
      (fun w => pullbackMatrix (openRestrictedField M S hS g.form) e w p q) =ᶠ[𝓝 z]
        (fun w => pullbackMatrix g.form (ambientOpenChart M S hS e) w p q) := by
    filter_upwards [e.open_source.mem_nhds hz] with w hw
    exact congrFun (congrFun (ambientOpenChart_pullbackMatrix M S hS g.form e he hw) p) q
  have hwirt (p q : Fin n) (v : ComplexVector n) :
      wirt (fun w => pullbackMatrix (openRestrictedField M S hS g.form) e w p q) z v =
        wirt (fun w => pullbackMatrix g.form (ambientOpenChart M S hS e) w p q) z v := by
    unfold wirt
    rw [(hgerm p q).fderiv_eq]
  rw [hwirt, hwirt]
  apply smoothMetric_pullback_wirt_symm g (ambientOpenChart M S hS e)
    (ambientOpenChart_mdifferentiableOn M S hS e he)
  simpa only [ambientOpenChart_source] using hz

end Yau.NodeProofs.F01Aux
