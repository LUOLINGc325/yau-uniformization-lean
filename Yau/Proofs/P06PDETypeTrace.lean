import Yau.Proofs.P06PDETypeTraceTrace
import Yau.Proofs.P06PDETypeTraceSemigroup

/-! Three original P06 PDE consequences, for arbitrary solutions in the
unchanged bounded classes. -/
noncomputable section
namespace Yau.NodeProofs
open Yau Yau.Blueprint

 theorem P06_type_preservation_proved :
    ∀ (n : ℕ) (X : KahlerManifold n) (A : RealForm X.manifold 2)
      (U : ℝ → RealForm X.manifold 2), BoundedOneOneData X.metric.form A →
      IsBoundedFormHeat X.metric.form A U → ∀ t, 0 < t → RealOneOne (U t) := by
  intro n X A U hA hU t ht
  exact P06Aux.PDETypeTrace.boundedFormHeat_oneOne X A U hA hU t ht

 theorem P06_trace_commutation_proved :
    ∀ (n : ℕ) (X : KahlerManifold n), HodgeTraceCommutation X.metric.form := by
  intro n X
  exact P06Aux.PDETypeTrace.hodgeTraceCommutation X

 theorem P06_semigroup_law_proved :
    ∀ (n : ℕ) (X : KahlerManifold n), HodgeSemigroupLaw X.metric.form := by
  intro n X
  exact P06Aux.PDETypeTrace.hodgeSemigroupLaw X

end Yau.NodeProofs
