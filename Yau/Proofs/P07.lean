import Yau.Proofs.P07ScaledHeatConstruction
import Yau.Proofs.P07DyadicExhaustion
import Yau.Proofs.P07DistanceLevi
import Yau.Proofs.P06LipschitzHessianHeat
import Yau.Blueprint.Nodes

/-! The original controlled exhaustion, in every original complex dimension.
The heat input is precisely the already proved compact-exterior rough scalar
part of P06; no noncompact heat extension or supplied exhaustion is used. -/
noncomputable section
open scoped ContDiff
namespace Yau.NodeProofs
open Yau Yau.Blueprint P07Aux

theorem P07_proved : Yau.Blueprint.P07 := by
  intro n X o
  obtain ⟨A1, A2, hA1, hA2, hder⟩ := radialProfile_derivative_bounds
  obtain ⟨A, hA, hweak⟩ := P07DistanceLevi.radialTruncation_weakLeviUpper X o
    radialProfile radialProfile_contDiff radialProfile_monotone radialProfile_one
    A1 A2 hA1.le hA2.le hder
  obtain ⟨μ, hμ⟩ := Yau.Proofs.G02Aux.exists_riemannianVolume X.metric.form
    (Yau.LeafProofs.L12Aux.metricSmooth_of_smoothMetric X.metric)
  have hradial : ∀ L : ℝ, 0 < L →
      WeakLeviUpper X.metric.form (radialTruncation X.metric o L) (A / L ^ 2) := by
    intro L hL
    change WeakLeviUpper X.metric.form
      (fun x => radialProfile (distFrom X.metric.form o x ^ 2 / L ^ 2)) (A / L ^ 2)
    exact hweak L hL
  obtain ⟨v, D1, D2, hD1, hD2, hv⟩ := scaledCutoffs_of_roughHeat_radialWeak X o μ hμ
    (P06_Lipschitz_Hessian_heat_proved n X) hA hradial
  exact controlledExhaustion_of_scaledCutoffs X o hD1.le hD2.le hv

end Yau.NodeProofs
