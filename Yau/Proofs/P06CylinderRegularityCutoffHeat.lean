import Yau.Proofs.P06CylinderRegularityCanonicalHeat
import Yau.Proofs.P06CylinderRegularityCutoffCauchy

/-! Actual canonical cutoff solutions and their proved full-jet Cauchy
property. All regularity and localization inputs are discharged. -/
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1400000
open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux.CylinderReg
open Yau Yau.Blueprint Yau.Parabolic Yau.LeafProofs.L03

theorem exists_canonical_cutoff_heat {n k : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (o : M.Carrier) (χ : ℕ → M.Carrier → ℝ) (hχ : MetricCutoffFamily g.form o χ)
    (A : RealForm M k) (hA : SmoothRealForm A) :
    ∃ U : ℕ → ℝ → RealForm M k, ∀ j,
      U j 0 = CutoffTail.cutoffForm χ A j ∧ SmoothFormTime (U j) (Set.Ioi 0) ∧
      FormHeatEquation g.form (U j) ∧ ∀ t, 0 < t →
        ∃ hUt : L2RealForm g.form μ (U j t), realizeActualForm g μ (U j t) hUt =
          hodgeHeatHilbert g μ hμ k t (CutoffTail.cutoffDatum g μ hμ o χ hχ A hA j) := by
  have hex (j : ℕ) := exists_canonical_actual_heat g μ hμ
    (CutoffTail.cutoffForm χ A j) (CutoffTail.cutoffForm_l2 g μ hμ o χ hχ A hA j)
  choose U hU using hex
  exact ⟨U,hU⟩

end Yau.NodeProofs.P06Aux.CylinderReg
