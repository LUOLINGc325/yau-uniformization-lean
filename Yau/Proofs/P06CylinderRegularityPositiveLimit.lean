import Yau.Proofs.P06CylinderRegularityCutoffHeat
import Yau.Proofs.P06CylinderRegularityLimitTransfer

/-! Positive-time local smooth limits of the actual canonical cutoff heat.
The full-jet Cauchy hypothesis is supplied by the proved cylinder estimate. -/
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux.CylinderReg
open Yau Yau.Blueprint Yau.Parabolic Yau.LeafProofs.L03

def CanonicalCutoffHeat {n k : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (o : M.Carrier) (χ : ℕ → M.Carrier → ℝ) (hχ : MetricCutoffFamily g.form o χ)
    (A : RealForm M k) (hA : SmoothRealForm A) (Us : ℕ → ℝ → RealForm M k) : Prop :=
  ∀ j, Us j 0 = CutoffTail.cutoffForm χ A j ∧ SmoothFormTime (Us j) (Set.Ioi 0) ∧
    FormHeatEquation g.form (Us j) ∧ ∀ t, 0 < t →
      ∃ hUt : L2RealForm g.form μ (Us j t), realizeActualForm g μ (Us j t) hUt =
        hodgeHeatHilbert g μ hμ k t (CutoffTail.cutoffDatum g μ hμ o χ hχ A hA j)

theorem canonicalCutoff_jointJetCauchy {n k : ℕ} (X : KahlerManifold n)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    (o : Pt X) (χ : ℕ → Pt X → ℝ) (hχ : MetricCutoffFamily X.metric.form o χ)
    (A : RealForm X.manifold k) (hA : SmoothRealForm A)
    (B : ℝ) (hb : ∀ x, formNormSq X.metric.form A x ≤ B^2)
    (Us : ℕ → ℝ → RealForm X.manifold k)
    (hUs : CanonicalCutoffHeat X.metric μ hμ o χ hχ A hA Us) :
    LocalCauchyLimit.JointJetCauchy Us := by
  choose hUL hUR using fun j t ht => (hUs j).2.2.2 t ht
  have hc := cutoff_actual_joint_jets_cauchy X μ hμ o o χ χ hχ hχ A hA B hb Us Us
    (fun j _ => (hUs j).2.1) (fun j _ => (hUs j).2.1)
    (fun j _ => (hUs j).2.2.1) (fun j _ => (hUs j).2.2.1)
    (fun j _ => hUL j) (fun j _ => hUL j)
    (fun j _ => hUR j) (fun j _ => hUR j)
  intro x K hK hKx eps T heps heT m I η hη
  obtain ⟨N,_,hN⟩ := hc x K hK hKx eps T heps heT m I η hη
  exact ⟨N,fun j hj l hl => hN j l hj hl⟩

theorem exists_canonical_cutoff_positive_limit {n k : ℕ} (X : KahlerManifold n)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    (o : Pt X) (χ : ℕ → Pt X → ℝ) (hχ : MetricCutoffFamily X.metric.form o χ)
    (A : RealForm X.manifold k) (hA : SmoothRealForm A)
    (B : ℝ) (hb : ∀ x, formNormSq X.metric.form A x ≤ B^2) :
    ∃ (Us : ℕ → ℝ → RealForm X.manifold k) (U : ℝ → RealForm X.manifold k),
      CanonicalCutoffHeat X.metric μ hμ o χ hχ A hA Us ∧ U 0=A ∧
      SmoothFormTime U (Set.Ioi 0) ∧ LocalCauchyLimit.JointJetLimit Us U := by
  obtain ⟨Us,hUs⟩ := exists_canonical_cutoff_heat X.metric μ hμ o χ hχ A hA
  obtain ⟨U,hzero,hU,hLimit⟩ := LocalCauchyLimit.exists_smooth_limit Us
    (fun j => (hUs j).2.1) (canonicalCutoff_jointJetCauchy X μ hμ o χ hχ A hA B hb Us hUs) A
  exact ⟨Us,U,hUs,hzero,hU,hLimit⟩

end Yau.NodeProofs.P06Aux.CylinderReg
