import Yau.Proofs.P06SmallTimeTailAnnuli
import Yau.Proofs.P06ScalarUniquenessRicciPositive

/-! Original Hodge heat has a support-independent Gaussian remote tail at
small times.  Both the Davies constant and the Ricci sign are supplied by
proved theorems for the original manifold. -/
noncomputable section
open MeasureTheory Filter Finset
open scoped Topology InnerProductSpace ComplexOrder

namespace Yau.NodeProofs.P06Aux.SmallTimeTail
open Yau Yau.Blueprint Yau.LeafProofs Yau.LeafProofs.L03 Davies CutoffTail
variable {n k : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false

theorem remote_smallTime_bound_of_nonnegativeRicci
    (g : SmoothMetric M) (hK : IsKahler g)
    (hRic : ∀ x, (ricci g.form x).PosSemidef)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (o : M.Carrier) (r : ℝ) (hr : 0 < r) :
    ∃ A : ℝ, 1 ≤ A ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (J : ℕ), 2 * r ≤ radius J →
      ∀ (B : ℝ), 0 ≤ B → ∀ (τ : ℝ), 0 < τ → τ ≤ 1 →
      ∀ (D : RealForm M k) (hD : L2RealForm g.form μ D),
      CompactlySupportedRealForm D → (∀ x, formNormSq g.form D x ≤ B ^ 2) →
      ballProjection g μ o J (realizeActualForm g μ D hD) = 0 →
      ∀ (t : ℝ), 0 < t → t ≤ 2 * τ →
      ‖indicator g μ (distBall g.form o r) (L12Aux.measurableSet_distBall g o r)
        (hodgeHeatHilbert g μ hμ k t (realizeActualForm g μ D hD))‖ ≤
        C * B * radius J ^ n * Real.exp (-radius J ^ 2 / (32 * A ^ 2 * τ)) := by
  obtain ⟨A, hA, htail⟩ := exists_uniform_annular_heat_L2_tail n
  exact ⟨A, hA, remote_smallTime_bound_of_annular g hK hRic μ hμ o A hA
    (htail M g μ hμ k o) r hr⟩

/-- The unconditional GT endpoint for the original paper's manifold and
the original all-degree Hodge semigroup. -/
theorem remote_smallTime_bound (X : KahlerManifold n)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    (o : Pt X) (r : ℝ) (hr : 0 < r) :
    ∃ A : ℝ, 1 ≤ A ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (J : ℕ), 2 * r ≤ radius J →
      ∀ (B : ℝ), 0 ≤ B → ∀ (τ : ℝ), 0 < τ → τ ≤ 1 →
      ∀ (D : RealForm X.manifold k) (hD : L2RealForm X.metric.form μ D),
      CompactlySupportedRealForm D → (∀ x, formNormSq X.metric.form D x ≤ B ^ 2) →
      ballProjection X.metric μ o J (realizeActualForm X.metric μ D hD) = 0 →
      ∀ (t : ℝ), 0 < t → t ≤ 2 * τ →
      ‖indicator X.metric μ (distBall X.metric.form o r)
        (L12Aux.measurableSet_distBall X.metric o r)
        (hodgeHeatHilbert X.metric μ hμ k t (realizeActualForm X.metric μ D hD))‖ ≤
        C * B * radius J ^ n * Real.exp (-radius J ^ 2 / (32 * A ^ 2 * τ)) :=
  remote_smallTime_bound_of_nonnegativeRicci X.metric X.kahler_metric
    (kahlerManifold_ricci_posSemidef X) μ hμ o r hr

end Yau.NodeProofs.P06Aux.SmallTimeTail
