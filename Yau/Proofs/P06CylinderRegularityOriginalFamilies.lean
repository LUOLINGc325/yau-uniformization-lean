import Yau.Proofs.P06CylinderRegularityPositiveLimit
import Yau.Proofs.P06L2HeatExistence

/-! Every solution family in the original L² PDE class has the same
positive-time smooth limit as the canonical cutoff family. -/
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux.CylinderReg
open Yau Yau.Blueprint Yau.Parabolic Yau.LeafProofs.L03

theorem original_cutoff_jointJetLimit {n : ℕ} (X : KahlerManifold n)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    (o : Pt X) (χ : ℕ → Pt X → ℝ) (hχ : MetricCutoffFamily X.metric.form o χ)
    (A : RealForm X.manifold 2) (hA : SmoothRealForm A)
    (B : ℝ) (hb : ∀ x, formNormSq X.metric.form A x ≤ B^2)
    (Us : ℕ → ℝ → RealForm X.manifold 2)
    (hUs : CanonicalCutoffHeat X.metric μ hμ o χ hχ A hA Us)
    (U : ℝ → RealForm X.manifold 2) (hU : SmoothFormTime U (Set.Ioi 0))
    (hLimit : LocalCauchyLimit.JointJetLimit Us U)
    (o' : Pt X) (χ' : ℕ → Pt X → ℝ) (hχ' : MetricCutoffFamily X.metric.form o' χ')
    (Vs : ℕ → ℝ → RealForm X.manifold 2)
    (hVs : ∀ j, 1 ≤ j → IsL2FormHeat X.metric.form μ (fun x => χ' j x • A x) (Vs j)) :
    FormHeatLocalSmoothLimit Vs U := by
  choose hUL hUR using fun j t ht => (hUs j).2.2.2 t ht
  apply jointJetLimit_of_mixed_cauchy Us Vs U (fun j _ => (hUs j).2.1)
    (fun j hj => (hVs j hj).2.2.1) hU hLimit
  apply cutoff_actual_joint_jets_cauchy X μ hμ o o' χ χ' hχ hχ' A hA B hb Us Vs
    (fun j _ => (hUs j).2.1) (fun j hj => (hVs j hj).2.2.1)
    (fun j _ => (hUs j).2.2.1) (fun j hj => (hVs j hj).2.2.2.1)
    (fun j _ => hUL j) (fun j hj => (hVs j hj).2.2.2.2.1)
    (fun j _ => hUR j)
  intro j hj t ht
  rw [CutoffTail.cutoffDatum_eq_actual X.metric μ hμ o' χ' hχ' A hA j hj]
  exact L2HeatExistence.isL2FormHeat_realization X.metric μ hμ _
    (metricCutoff_smooth_l2 X.metric μ hμ o' χ' hχ' A hA j hj) _ (hVs j hj) ht

end Yau.NodeProofs.P06Aux.CylinderReg
