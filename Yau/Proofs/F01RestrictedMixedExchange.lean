import Yau.Proofs.F01RestrictedKahlerJets
import Yau.Proofs.F01KahlerMixedExchange
import Yau.Proofs.F01ChartGramSmooth
import Yau.Proofs.F01OpenMetricSmooth

/-! The actual restricted Kähler background has the second-derivative
cancellation used in the conformal Rayleigh evolution. -/
noncomputable section
open Set TopologicalSpace
open scoped Manifold ContDiff Matrix
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs.L17Aux
variable {n : ℕ} (M : ComplexManifold n) (S : Opens M.Carrier)
  (hS : IsConnected (S : Set M.Carrier))

theorem restricted_metric_diagonal_mixed_exchange (g : SmoothMetric M)
    (e : OpenPartialHomeomorph (ComplexVector n) (openConnectedManifold M S hS).Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    {z : ComplexVector n} (hz : z ∈ e.source) (i a : Fin n) :
    wirt (fun w => wirtBar
      (fun y => pullbackMatrix (openRestrictedField M S hS g.form) e y i i) w (stdVec a)) z (stdVec a) =
    wirt (fun w => wirtBar
      (fun y => pullbackMatrix (openRestrictedField M S hS g.form) e y a a) w (stdVec i)) z (stdVec i) := by
  apply kahler_diagonal_mixed_exchange
    (pullbackMatrix (openRestrictedField M S hS g.form) e)
    (fun w => pullbackMatrix_isHermitian _ e w) e.open_source hz
  · intro p q
    exact (pullbackMatrix_entry_contDiffAt _
      (openRestrictedField_metricSmooth M S hS (Yau.LeafProofs.L12Aux.metricSmooth_of_smoothMetric g))
      e he hz p q).of_le (by simp)
  · intro w hw p q l
    exact restricted_metric_pullback_wirt_symm M S hS g e he hw p q l

end Yau.NodeProofs.F01Aux
