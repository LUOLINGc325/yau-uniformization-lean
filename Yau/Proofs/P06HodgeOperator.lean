import Yau.Proofs.P06PositiveResolvent
import Yau.Proofs.P06HodgeResolvent

noncomputable section
open MeasureTheory
open scoped Topology InnerProductSpace

namespace Yau.NodeProofs.P06Aux
open Yau Yau.LeafProofs.L03
variable {n : ℕ} {M : ComplexManifold n}

def hodgeCompleteOperator (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (k : ℕ) :
    L2FormHilbert g μ k →ₗ.[ℝ] L2FormHilbert g μ k :=
  (hodgeCoreOperator g μ hμ k).closure

theorem hodgeCompleteOperator_dense (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (k : ℕ) :
    Dense ((hodgeCompleteOperator g μ hμ k).domain : Set (L2FormHilbert g μ k)) :=
  (hodgeCoreOperator_domain_dense g μ hμ k).mono (hodgeCoreOperator g μ hμ k).le_closure.1

theorem hodgeCompleteOperator_selfAdjoint (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (k : ℕ) :
    (hodgeCompleteOperator g μ hμ k).adjoint = hodgeCompleteOperator g μ hμ k :=
  realClosure_selfAdjoint (hodgeCoreOperator g μ hμ k)
    (hodgeCoreOperator_domain_dense g μ hμ k) (hodgeCoreOperator_closable g μ hμ k)
    (hodgeCoreOperator_symmetric g μ hμ k) (hodgeCoreOperator_closure_eq_adjoint g μ hμ k)

theorem hodgeCompleteOperator_nonnegative (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (k : ℕ)
    (u : (hodgeCompleteOperator g μ hμ k).domain) :
    0 ≤ inner ℝ (u : L2FormHilbert g μ k) (hodgeCompleteOperator g μ hμ k u) :=
  realClosure_nonnegative (hodgeCoreOperator g μ hμ k) (hodgeCoreOperator_closable g μ hμ k)
    (hodgeCoreOperator_nonnegative g μ hμ k) u

def hodgeResolventOne (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (k : ℕ) : L2FormHilbert g μ k →L[ℝ] L2FormHilbert g μ k :=
  positiveResolvent (hodgeCompleteOperator g μ hμ k) (hodgeCompleteOperator_dense g μ hμ k)
    (hodgeCompleteOperator_selfAdjoint g μ hμ k) (hodgeCompleteOperator_nonnegative g μ hμ k)
    1 zero_lt_one

theorem hodgeResolventOne_graph (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (k : ℕ) (f : L2FormHilbert g μ k) :
    (hodgeResolventOne g μ hμ k f, f - hodgeResolventOne g μ hμ k f) ∈
      (hodgeCompleteOperator g μ hμ k).graph := by
  simpa only [hodgeResolventOne, one_smul] using positiveResolvent_graph (hodgeCompleteOperator g μ hμ k)
    (hodgeCompleteOperator_dense g μ hμ k) (hodgeCompleteOperator_selfAdjoint g μ hμ k)
    (hodgeCompleteOperator_nonnegative g μ hμ k) 1 zero_lt_one f

theorem hodgeResolventOne_symmetric (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (k : ℕ) : (hodgeResolventOne g μ hμ k).IsSymmetric :=
  positiveResolvent_symmetric (hodgeCompleteOperator g μ hμ k) (hodgeCompleteOperator_dense g μ hμ k)
    (hodgeCompleteOperator_selfAdjoint g μ hμ k) (hodgeCompleteOperator_nonnegative g μ hμ k) 1 zero_lt_one

theorem hodgeResolventOne_positive (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (k : ℕ) (f : L2FormHilbert g μ k) :
    0 ≤ inner ℝ (hodgeResolventOne g μ hμ k f) f :=
  positiveResolvent_inner_nonnegative (hodgeCompleteOperator g μ hμ k)
    (hodgeCompleteOperator_dense g μ hμ k) (hodgeCompleteOperator_selfAdjoint g μ hμ k)
    (hodgeCompleteOperator_nonnegative g μ hμ k) 1 zero_lt_one f

theorem hodgeResolventOne_bound (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (k : ℕ) (f : L2FormHilbert g μ k) :
    ‖hodgeResolventOne g μ hμ k f‖ ≤ ‖f‖ := by
  simpa only [hodgeResolventOne, inv_one, one_mul] using positiveResolvent_bound (hodgeCompleteOperator g μ hμ k)
    (hodgeCompleteOperator_dense g μ hμ k) (hodgeCompleteOperator_selfAdjoint g μ hμ k)
    (hodgeCompleteOperator_nonnegative g μ hμ k) 1 zero_lt_one f

theorem hodgeResolventOne_injective (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (k : ℕ) : Function.Injective (hodgeResolventOne g μ hμ k) :=
  positiveResolvent_injective (hodgeCompleteOperator g μ hμ k) (hodgeCompleteOperator_dense g μ hμ k)
    (hodgeCompleteOperator_selfAdjoint g μ hμ k) (hodgeCompleteOperator_nonnegative g μ hμ k) 1 zero_lt_one

end Yau.NodeProofs.P06Aux
