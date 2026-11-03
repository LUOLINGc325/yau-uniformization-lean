import Yau.Proofs.P06ScalarSmoothHeatMetricTrace
import Yau.Proofs.P06ScalarSmoothHeatZero
import Yau.Proofs.P06PDETypeTraceTrace

/-! The original scalar existence and uniqueness clause follows from the
original bounded Hodge existence clause. The parent constructs that clause
internally; this implication adds no assumption to the final P06 target. -/
noncomputable section
open MeasureTheory
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux.ScalarSmooth
open Yau Yau.Blueprint
variable {n : ℕ}

theorem scalarHeatExistenceUniqueness_of_hodge (X : KahlerManifold n)
    (hH : HodgeHeatExistenceUniqueness X.metric.form) :
    ScalarHeatExistenceUniqueness X.metric.form := by
  intro f hf hb
  refine ⟨?_,fun u v hu hv t ht => PDETypeTrace.boundedScalarHeat_unique X f u v hu hv t ht⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨fun _ => f,boundedScalarHeat_zeroDim X.metric.form f hf hb⟩
  · have hA := scalarTraceDatum_bounded X.metric f hf hb hn
    obtain ⟨U,hU⟩ := (hH (scalarTraceDatum X.metric.form f) hA).1
    have hu := PDETypeTrace.trace_boundedScalarHeat X hA hU
    rw [scalarTraceDatum_trace X.metric.form f hn] at hu
    exact ⟨_,hu⟩

end Yau.NodeProofs.P06Aux.ScalarSmooth
