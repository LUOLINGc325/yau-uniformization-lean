import Yau.Proofs.P06SmoothFormOrder

noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace

namespace Yau.NodeProofs.P06Aux
open Yau Yau.LeafProofs.L03
variable {n : ℕ} {M : ComplexManifold n}

theorem oneOne_smooth_representative (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A : RealForm M 2)
    (hA : SmoothRealForm A) (hAL : L2RealForm g.form μ A)
    (htype : oneOneProjectionHilbert g μ (realizeActualForm g μ A hAL) =
      realizeActualForm g μ A hAL) : RealOneOne A := by
  rw [oneOneProjectionHilbert_realize] at htype
  have hae := (realizeL2Form_eq_iff_ae g μ
    (L2FormSpace.ofSection (P06Weitzenbock.oneOneProjection A) (l2RealForm_oneOneProjection g μ A hAL))
    (L2FormSpace.ofSection A hAL)).mp htype
  have he := smoothRealForm_eq_of_ae g μ hμ (P06Weitzenbock.oneOneProjection A) A
    (P06Weitzenbock.oneOneProjection_smooth A hA) hA hae
  rw [← he]
  exact P06Weitzenbock.oneOneProjection_type A

/-- Every smooth actual representative of the original heat has the
original pointwise (1,1) type, before any bounded-solution construction. -/
theorem hodgeHeat_smooth_representative_oneOne (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (hk : IsKahler g)
    (A B : RealForm M 2) (hA : L2RealForm g.form μ A) (h11 : RealOneOne A)
    (hB : SmoothRealForm B) (hBL : L2RealForm g.form μ B)
    (t : ℝ) (ht : 0 ≤ t)
    (he : realizeActualForm g μ B hBL = hodgeHeatHilbert g μ hμ 2 t (realizeActualForm g μ A hA)) :
    RealOneOne B := by
  apply oneOne_smooth_representative g μ hμ B hB hBL
  rw [he]
  apply hodgeHeatHilbert_oneOne g μ hμ hk _ _ t ht
  rw [oneOneProjectionHilbert_realize]
  exact realizeActualForm_congr g μ _ _ _ _ (P06Weitzenbock.oneOneProjection_fixed A h11)

/-- The original CFC heat preserves the literal same-C pointwise signed
form bound on any smooth actual L² representative. -/
theorem hodgeHeat_smooth_representative_order (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (hk : IsKahler g)
    (hHBC : ∀ x u v, 0 ≤ paperHolomorphicBisectionalCurvature g.form x u v)
    (A B : RealForm M 2) (hA : L2RealForm g.form μ A) (h11 : RealOneOne A)
    {C : ℝ} (hC : 0 ≤ C) (hbound : FormOrderBound g.form C A)
    (hB : SmoothRealForm B) (hBL : L2RealForm g.form μ B)
    (t : ℝ) (ht : 0 ≤ t)
    (he : realizeActualForm g μ B hBL = hodgeHeatHilbert g μ hμ 2 t (realizeActualForm g μ A hA)) :
    FormOrderBound g.form C B := by
  apply intervalCone_smooth_representative g μ hμ B hB hBL
    (hodgeHeat_smooth_representative_oneOne g μ hμ hk A B hA h11 hB hBL t ht he) hC
  rw [he]
  exact hodgeHeatHilbert_interval g μ hμ hk hHBC hC _
    (realizeActualForm_mem_hodgeL2IntervalCone g μ A hA h11 hbound) t ht

theorem hodgeHeat_smooth_representative_positive (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (hk : IsKahler g)
    (hHBC : ∀ x u v, 0 ≤ paperHolomorphicBisectionalCurvature g.form x u v)
    (A B : RealForm M 2) (hA : L2RealForm g.form μ A) (h11 : RealOneOne A)
    (hp : FormLE 0 A) (hB : SmoothRealForm B) (hBL : L2RealForm g.form μ B)
    (t : ℝ) (ht : 0 ≤ t)
    (he : realizeActualForm g μ B hBL = hodgeHeatHilbert g μ hμ 2 t (realizeActualForm g μ A hA)) :
    FormLE 0 B := by
  apply positiveCone_smooth_representative g μ hμ B hB hBL
    (hodgeHeat_smooth_representative_oneOne g μ hμ hk A B hA h11 hB hBL t ht he)
  rw [he]
  exact hodgeHeatHilbert_positive g μ hμ hk hHBC _
    (realizeActualForm_mem_hodgeL2PositiveCone g μ A hA h11 hp) t ht

end Yau.NodeProofs.P06Aux
