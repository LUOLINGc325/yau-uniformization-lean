import Yau.Proofs.P06CylinderRegularityPositiveLimit
import Yau.Proofs.P06CylinderRegularityFormLinear

/-! The actual difference of two canonical cutoff heats realizes the
heat of the actual initial cutoff difference. -/
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory

namespace Yau.NodeProofs.P06Aux.CylinderReg
open Yau Yau.Blueprint Yau.LeafProofs.L03

theorem canonicalCutoff_difference_realization {n k : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (o : M.Carrier) (χ : ℕ → M.Carrier → ℝ) (hχ : MetricCutoffFamily g.form o χ)
    (A : RealForm M k) (hA : SmoothRealForm A) (Us : ℕ → ℝ → RealForm M k)
    (hUs : CanonicalCutoffHeat g μ hμ o χ hχ A hA Us) (j l : ℕ) (t : ℝ) (ht : 0 < t) :
    ∃ hD : L2RealForm g.form μ (Us l t-Us j t),
      realizeActualForm g μ (Us l t-Us j t) hD =
        hodgeHeatHilbert g μ hμ k t
          (CutoffTail.cutoffDatum g μ hμ o χ hχ A hA l-
            CutoffTail.cutoffDatum g μ hμ o χ hχ A hA j) := by
  obtain ⟨hl,hrl⟩ := (hUs l).2.2.2 t ht
  obtain ⟨hj,hrj⟩ := (hUs j).2.2.2 t ht
  refine ⟨l2RealForm_sub g μ _ _ hl hj,?_⟩
  rw [realizeActualForm_sub g μ (Us l t) (Us j t) hl hj,hrl,hrj,map_sub]

end Yau.NodeProofs.P06Aux.CylinderReg
