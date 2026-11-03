import Yau.Proofs.P06HeatPointwiseOrder

noncomputable section
open MeasureTheory
open scoped Topology InnerProductSpace

namespace Yau.NodeProofs.P06Aux
open Yau Yau.LeafProofs.L03
variable {n : ℕ} {M : ComplexManifold n}

/-- Pointwise comparison of arbitrary smooth representatives follows from
linearity of the same original heat and its genuine positive-cone theorem. -/
theorem hodgeHeat_smooth_representatives_comparison (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (hk : IsKahler g)
    (hHBC : ∀ x u v, 0 ≤ paperHolomorphicBisectionalCurvature g.form x u v)
    (A B U V : RealForm M 2) (hA : L2RealForm g.form μ A) (hB : L2RealForm g.form μ B)
    (h11A : RealOneOne A) (h11B : RealOneOne B) (hAB : FormLE A B)
    (hU : SmoothRealForm U) (hUL : L2RealForm g.form μ U)
    (hV : SmoothRealForm V) (hVL : L2RealForm g.form μ V)
    (t : ℝ) (ht : 0 ≤ t)
    (heU : realizeActualForm g μ U hUL = hodgeHeatHilbert g μ hμ 2 t (realizeActualForm g μ A hA))
    (heV : realizeActualForm g μ V hVL = hodgeHeatHilbert g μ hμ 2 t (realizeActualForm g μ B hB)) :
    FormLE U V := by
  have hD : L2RealForm g.form μ (B - A) := l2RealForm_sub g μ B A hB hA
  have hZ : L2RealForm g.form μ (V - U) := l2RealForm_sub g μ V U hVL hUL
  have hp : FormLE 0 (B - A) := by
    intro x
    simpa only [formHermitianMatrix_sub, formHermitianMatrix_zero, sub_zero] using hAB x
  have he : realizeActualForm g μ (V - U) hZ =
      hodgeHeatHilbert g μ hμ 2 t (realizeActualForm g μ (B - A) hD) := by
    rw [realizeActualForm_sub g μ V U hVL hUL,
      realizeActualForm_sub g μ B A hB hA, map_sub, heU, heV]
  have hz := hodgeHeat_smooth_representative_positive g μ hμ hk hHBC
    (B - A) (V - U) hD (realOneOne_sub B A h11B h11A) hp
    ((smoothFormSubmodule (M := M) 2).sub_mem hV hU) hZ t ht he
  intro x
  simpa only [formHermitianMatrix_sub, formHermitianMatrix_zero, sub_zero] using hz x

theorem hodgeHeat_smooth_representative_norm (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (hk : IsKahler g)
    (hHBC : ∀ x u v, 0 ≤ paperHolomorphicBisectionalCurvature g.form x u v)
    (A B : RealForm M 2) (hA : L2RealForm g.form μ A) (h11 : RealOneOne A)
    {C : ℝ} (hC : 0 ≤ C) (hbound : FormOrderBound g.form C A)
    (hB : SmoothRealForm B) (hBL : L2RealForm g.form μ B)
    (t : ℝ) (ht : 0 ≤ t)
    (he : realizeActualForm g μ B hBL = hodgeHeatHilbert g μ hμ 2 t (realizeActualForm g μ A hA))
    (x : M.Carrier) : formNormSq g.form B x ≤ (n : ℝ) * C ^ 2 :=
  G04Aux.norm_of_order g.form B
    (hodgeHeat_smooth_representative_oneOne g μ hμ hk A B hA h11 hB hBL t ht he) hC
    (hodgeHeat_smooth_representative_order g μ hμ hk hHBC A B hA h11 hC hbound hB hBL t ht he) x

end Yau.NodeProofs.P06Aux
