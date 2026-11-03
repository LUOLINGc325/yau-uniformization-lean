import Yau.Proofs.P06ScalarUniquenessVolume
import Yau.Proofs.P06ScalarUniquenessRicciPositive
import Yau.Proofs.G02

/-! Uniqueness in the original bounded scalar heat class, from the original
Kähler manifold data and continuous initial trace alone. -/
noncomputable section
open MeasureTheory
namespace Yau.NodeProofs.P06Aux
open Yau Yau.Blueprint
variable {n : ℕ}

theorem continuousInitialScalarHeat_unique (X : KahlerManifold n)
    (f : Pt X → ℝ) (u v : ℝ → Pt X → ℝ)
    (hu : IsContinuousInitialScalarHeat X.metric.form f u)
    (hv : IsContinuousInitialScalarHeat X.metric.form f v) :
    ∀ t, 0 < t → u t = v t := by
  obtain ⟨μ, hμ⟩ := Yau.Proofs.G02Aux.exists_riemannianVolume X.metric.form
    (Yau.LeafProofs.L12Aux.metricSmooth_of_smoothMetric X.metric)
  exact continuousInitialScalarHeat_unique_of_nonnegativeRicci X.metric X.kahler_metric
    (kahlerManifold_ricci_posSemidef X) μ hμ f u v hu hv

end Yau.NodeProofs.P06Aux

namespace Yau.NodeProofs
open Yau Yau.Blueprint

/-- The full uniqueness projection of the original P06 rough heat clause. -/
theorem P06_rough_uniqueness_proved :
    ∀ (n : ℕ) (X : KahlerManifold n) (f : Pt X → ℝ) (u v : ℝ → Pt X → ℝ),
      IsContinuousInitialScalarHeat X.metric.form f u →
      IsContinuousInitialScalarHeat X.metric.form f v →
      ∀ t, 0 < t → u t = v t := by
  intro n X f u v hu hv
  exact P06Aux.continuousInitialScalarHeat_unique X f u v hu hv

end Yau.NodeProofs
