import Yau.Proofs.P06L2HeatExistenceInitial
import Yau.Proofs.P06HodgeRegularityHeatEquation

/-! An actual smooth heat representative for every original rough L² datum. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff InnerProductSpace ENNReal

namespace Yau.NodeProofs.P06Aux.L2HeatExistence
open Yau Yau.Blueprint Yau.LeafProofs.L03
variable {n k : ℕ} {M : ComplexManifold n}

/-- Fix the actual value at the initial face without changing positive-time jets. -/
def initialExtension (A : RealForm M k) (U : ℝ → RealForm M k) : ℝ → RealForm M k :=
  fun t => if 0 < t then U t else A

@[simp] theorem initialExtension_zero (A : RealForm M k) (U : ℝ → RealForm M k) :
    initialExtension A U 0 = A := by simp [initialExtension]

theorem initialExtension_pos (A : RealForm M k) (U : ℝ → RealForm M k)
    {t : ℝ} (ht : 0 < t) : initialExtension A U t = U t := ite_eq_left ht

theorem initialExtension_smooth (A : RealForm M k) (U : ℝ → RealForm M k)
    (hU : SmoothFormTime U (Ioi 0)) : SmoothFormTime (initialExtension A U) (Ioi 0) := by
  intro x I
  apply (hU x I).congr
  intro p hp
  rw [initialExtension_pos A U hp.2]

theorem initialExtension_heatEquation (g : HermitianField M)
    (A : RealForm M k) (U : ℝ → RealForm M k) (hU : FormHeatEquation g U) :
    FormHeatEquation g (initialExtension A U) := by
  intro x z hz t ht I
  rw [initialExtension_pos A U ht]
  apply (hU x z hz t ht I).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ht] with s hs
  rw [initialExtension_pos A U hs]

/-- The same complete Hilbert heat has an actual representative with the exact
raw initial value, original computed PDE, and original L² initial/energy class. -/
theorem exists_isL2FormHeat (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A : RealForm M 2) (hA : L2RealForm g.form μ A) :
    ∃ U : ℝ → RealForm M 2, IsL2FormHeat g.form μ A U ∧
      ∀ t, 0 < t → ∃ hUt : L2RealForm g.form μ (U t),
        realizeActualForm g μ (U t) hUt =
          hodgeHeatHilbert g μ hμ 2 t (realizeActualForm g μ A hA) := by
  obtain ⟨V, hVs, hVeq, hVr⟩ := hodgeStrongPath_geometric_regularity g μ hμ
    (fun t => hodgeHeatHilbert g μ hμ 2 t (realizeActualForm g μ A hA))
    (hodgeHeatHilbert_strongPath g μ hμ 2 (realizeActualForm g μ A hA))
  let U := initialExtension A V
  have hUr : ∀ t, 0 < t → ∃ hUt : L2RealForm g.form μ (U t),
      realizeActualForm g μ (U t) hUt =
        hodgeHeatHilbert g μ hμ 2 t (realizeActualForm g μ A hA) := by
    intro t ht
    dsimp only [U]
    rw [initialExtension_pos A V ht]
    exact hVr t ht
  refine ⟨U, ⟨hA, initialExtension_zero A V, initialExtension_smooth A V hVs,
    initialExtension_heatEquation g.form A V hVeq, ?_,
    heatRealization_initial g μ hμ A hA U hUr, ?_⟩, hUr⟩
  · intro t ht
    exact (hUr t ht).choose
  · intro T hT
    refine ⟨‖realizeActualForm g μ A hA‖ ^ 2 + 1, by positivity, ?_⟩
    intro t ht htT
    exact (heatRealization_lintegral_bound g μ hμ A hA U hUr t ht).trans
      (ENNReal.ofReal_le_ofReal (by linarith))

end Yau.NodeProofs.P06Aux.L2HeatExistence
