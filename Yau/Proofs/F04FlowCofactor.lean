import Yau.Proofs.F04CofactorGeneral
import Yau.Proofs.F04Source

/-! The cofactor bound for the same localized flow and its actual density. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder

noncomputable section

namespace Yau.F04Proof

open Yau.Blueprint

variable {n : ℕ} {X : KahlerManifold n}

theorem flow_cofactor_trace_bound (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ) (x : Pt X) (t : ℝ) (ht : 0 ≤ t) :
    density ρ x t * traceWith (gMat (h t) x) (gMat X.metric.form x) ≤ n := by
  rw [density_eq_det_ratio o h U P ρ hloc x t ht]
  exact cofactor_trace_bound _ _
    (LeafProofs.L18Aux.hMat_posDef X.metric.form x (chartPt x x) (mem_extChartAt_target x))
    (LeafProofs.L18Aux.hMat_posDef (h t) x (chartPt x x) (mem_extChartAt_target x))
    (hloc.2.2.2.2.1 t ht x)

end Yau.F04Proof
