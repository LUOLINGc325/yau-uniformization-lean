import Yau.Proofs.P06CylinderRegularityPositiveLimit
import Yau.Proofs.P06ScalarSmoothHeatCompactInitial

/-! Each actual compact cutoff heat attains its initial form in every
original spatial jet. This is the proved compact-data theorem. -/
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1400000
open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux.CylinderReg
open Yau Yau.Blueprint Yau.LeafProofs.L03

theorem canonicalCutoff_smoothInitial {n k : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (o : M.Carrier) (χ : ℕ → M.Carrier → ℝ) (hχ : MetricCutoffFamily g.form o χ)
    (A : RealForm M k) (hA : SmoothRealForm A) (Us : ℕ → ℝ → RealForm M k)
    (hUs : CanonicalCutoffHeat g μ hμ o χ hχ A hA Us) (j : ℕ) :
    FormSmoothInitial (Us j) (CutoffTail.cutoffForm χ A j) := by
  let Aj := CutoffTail.cutoffForm χ A j
  have hsAj : SmoothRealForm Aj := smoothRealForm_multiply _ A
    (CutoffTail.cutoffScalar_smooth g o χ hχ j) hA
  have hcAj : CompactlySupportedRealForm Aj := CutoffTail.cutoffForm_compact g o χ hχ A j
  choose hUL hUR using (hUs j).2.2.2
  apply ScalarSmooth.hodgeHeat_compact_initial g μ hμ Aj hsAj hcAj (Us j)
    (fun t ht => smoothFormTime_slice (hUs j).2.1 ht) hUL ?_ (hUs j).1
  intro t ht
  exact hUR t ht

end Yau.NodeProofs.P06Aux.CylinderReg
