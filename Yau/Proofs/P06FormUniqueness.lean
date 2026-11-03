import Yau.Proofs.P06FormUniquenessVolume
import Yau.Proofs.P06ScalarUniquenessRicciPositive
import Yau.Proofs.G02

/-! Uniqueness in the unchanged bounded form heat class. -/
noncomputable section
open MeasureTheory
namespace Yau.NodeProofs.P06Aux
open Yau Yau.Blueprint
variable {n k : ℕ}

theorem boundedFormHeat_unique (X : KahlerManifold n)
    (A : RealForm X.manifold k) (U V : ℝ → RealForm X.manifold k)
    (hU : IsBoundedFormHeat X.metric.form A U)
    (hV : IsBoundedFormHeat X.metric.form A V) :
    ∀ t, 0 ≤ t → U t = V t := by
  obtain ⟨μ, hμ⟩ := Yau.Proofs.G02Aux.exists_riemannianVolume X.metric.form
    (Yau.LeafProofs.L12Aux.metricSmooth_of_smoothMetric X.metric)
  exact boundedFormHeat_unique_of_nonnegativeRicci X.metric X.kahler_metric
    (kahlerManifold_ricci_posSemidef X) μ hμ A U V hU hV

end Yau.NodeProofs.P06Aux

namespace Yau.NodeProofs
open Yau Yau.Blueprint

/-- The arbitrary-real-two-form uniqueness projection of the original P06
Hodge heat assertion, including time zero and signed initial forms. -/
theorem P06_form_uniqueness_proved :
    ∀ (n : ℕ) (X : KahlerManifold n) (A : RealForm X.manifold 2)
      (U V : ℝ → RealForm X.manifold 2),
      IsBoundedFormHeat X.metric.form A U → IsBoundedFormHeat X.metric.form A V →
        ∀ t, 0 ≤ t → U t = V t := by
  intro n X A U V hU hV
  exact P06Aux.boundedFormHeat_unique X A U V hU hV

end Yau.NodeProofs
