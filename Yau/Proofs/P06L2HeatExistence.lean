import Yau.Proofs.P06L2HeatExistenceRealization
import Yau.Proofs.P06FormUniquenessL2

/-! The original full L² Hodge heat construction and arbitrary-PDE uniqueness. -/
noncomputable section
open MeasureTheory

namespace Yau.NodeProofs
open Yau Yau.Blueprint

namespace P06Aux.L2HeatExistence
open Yau.LeafProofs.L03
variable {n : ℕ} {M : ComplexManifold n}

/-- Every solution in the original PDE class realizes the same complete heat,
including solutions supplied independently of the construction. -/
theorem isL2FormHeat_realization (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A : RealForm M 2) (hA : L2RealForm g.form μ A)
    (U : ℝ → RealForm M 2) (hU : IsL2FormHeat g.form μ A U) {t : ℝ} (ht : 0 < t) :
    realizeActualForm g μ (U t) (hU.2.2.2.2.1 t ht) =
      hodgeHeatHilbert g μ hμ 2 t (realizeActualForm g μ A hA) := by
  obtain ⟨V, hV, hVr⟩ := exists_isL2FormHeat g μ hμ A hA
  obtain ⟨hVt, hr⟩ := hVr t ht
  have he : U t = V t := l2FormHeat_unique g μ hμ A U V hU hV t ht.le
  simpa only [he] using hr

end P06Aux.L2HeatExistence

theorem P06_L2_heat_existence_proved :
    ∀ (n : ℕ) (X : KahlerManifold n) (μ : Measure X.manifold.Carrier),
      IsRiemannianVolume X.metric.form μ →
      ∀ A : RealForm X.manifold 2, L2RealForm X.metric.form μ A →
        ∃ U, IsL2FormHeat X.metric.form μ A U := by
  intro n X μ hμ A hA
  obtain ⟨U, hU, _⟩ := P06Aux.L2HeatExistence.exists_isL2FormHeat X.metric μ hμ A hA
  exact ⟨U, hU⟩

/-- No smoothness, type, pointwise bound, or selected evolution is required
of the original L² datum. Uniqueness covers every original PDE solution. -/
theorem P06_L2_Hodge_heat_proved :
    ∀ (n : ℕ) (X : KahlerManifold n) (μ : Measure X.manifold.Carrier),
      IsRiemannianVolume X.metric.form μ → L2HodgeHeatTarget X.metric.form μ := by
  intro n X μ hμ A hA
  exact ⟨P06_L2_heat_existence_proved n X μ hμ A hA,
    fun U V hU hV => P06_L2_form_uniqueness_proved n X μ hμ A U V hU hV⟩

end Yau.NodeProofs
