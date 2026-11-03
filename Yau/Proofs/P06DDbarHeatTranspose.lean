import Yau.Proofs.P06DDbarHeatDomain

noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace

namespace Yau.NodeProofs.P06Aux.DDbarHeat
open Yau Yau.LeafProofs Yau.LeafProofs.L03 G04Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem hodge_ddForm (g : SmoothMetric M) (hk : IsKahler g)
    (A : RealForm M 0) (hA : SmoothRealForm A) :
    hodgeRealForm g.form 2 (ddForm A) = ddForm (hodgeRealForm g.form 0 A) := by
  simpa only [ddForm,scalarForm_scalarValue] using
    hodge_dd g hk (WeakCurrent.scalarValue A) (WeakCurrent.scalarValue_smooth A hA)

/-- Compact formal transposition suffices; no degree-one J/Hodge assertion is used. -/
theorem adjoint_hodge (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (hk : IsKahler g)
    (B : RealForm M 2) (hB : SmoothRealForm B) (hcB : CompactlySupportedRealForm B) :
    realizeActualForm g μ (adjointForm g.form (hodgeRealForm g.form 2 B))
      (adjointForm_l2 g μ hμ _ (hodgeRealForm_smooth g μ hμ B hB)
        (hodgeRealForm_compactlySupported g μ hμ B hB hcB)) =
      realizeActualForm g μ (hodgeRealForm g.form 0 (adjointForm g.form B))
        (hodgeRealForm_l2 g μ hμ _ (adjointForm_smooth g μ hμ B hB)
          (adjointForm_compact g μ hμ B hB hcB)) := by
  apply sub_eq_zero.mp
  apply hilbert_zero_of_compact_form_pairings g μ hμ
  intro A hA hcA
  rw [inner_sub_left, sub_eq_zero]
  rw [realizeActualForm_inner,realizeActualForm_inner]
  rw [formInner_symm g.form (adjointForm g.form (hodgeRealForm g.form 2 B)) A,
    formInner_symm g.form (hodgeRealForm g.form 0 (adjointForm g.form B)) A]
  have hHB := hodgeRealForm_smooth g μ hμ B hB
  have hcHB := hodgeRealForm_compactlySupported g μ hμ B hB hcB
  calc
    _ = ∫ x, formInner g.form (ddForm A) (hodgeRealForm g.form 2 B) x ∂μ :=
      (integral_ddForm_adjoint g μ hμ A hA _ hHB hcHB).symm
    _ = ∫ x, formInner g.form (hodgeRealForm g.form 2 (ddForm A)) B x ∂μ :=
      by
        rw [formInner_symm g.form (ddForm A) (hodgeRealForm g.form 2 B)]
        exact (hodgeRealForm_symmetric g μ hμ _ B (ddForm_smooth A hA) hB
          (ddForm_compact A hA hcA) hcB).symm
    _ = ∫ x, formInner g.form (ddForm (hodgeRealForm g.form 0 A)) B x ∂μ := by
      rw [hodge_ddForm g hk A hA]
    _ = ∫ x, formInner g.form (hodgeRealForm g.form 0 A) (adjointForm g.form B) x ∂μ :=
      integral_ddForm_adjoint g μ hμ _ (hodgeRealForm_smooth g μ hμ A hA) B hB hcB
    _ = _ := by
      rw [formInner_symm g.form A (hodgeRealForm g.form 0 (adjointForm g.form B))]
      exact hodgeRealForm_symmetric g μ hμ A _ hA (adjointForm_smooth g μ hμ B hB)
        hcA (adjointForm_compact g μ hμ B hB hcB)

end Yau.NodeProofs.P06Aux.DDbarHeat
