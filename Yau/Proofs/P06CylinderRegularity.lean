import Yau.Proofs.P06CylinderRegularityRemoteInitial
import Yau.Proofs.P06CylinderRegularityPositiveHeat

/-! Actual canonical cutoff heat, complete original smooth initial trace,
and the original local smooth limit for every cutoff/evolution family. -/
noncomputable section
open MeasureTheory

namespace Yau.NodeProofs.P06Aux.CylinderReg
open Yau Yau.Blueprint

theorem exists_canonical_cutoff_heat_initial {n k : ℕ} (X : KahlerManifold n)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    (o : Pt X) (χ : ℕ → Pt X → ℝ) (hχ : MetricCutoffFamily X.metric.form o χ)
    (A : RealForm X.manifold k) (hA : SmoothRealForm A)
    (B : ℝ) (hb : ∀ x, formNormSq X.metric.form A x ≤ B^2) :
    ∃ (Us : ℕ → ℝ → RealForm X.manifold k) (U : ℝ → RealForm X.manifold k),
      CanonicalCutoffHeat X.metric μ hμ o χ hχ A hA Us ∧ U 0=A ∧
      SmoothFormTime U (Set.Ioi 0) ∧ FormHeatEquation X.metric.form U ∧
      FormSmoothInitial U A ∧ LocalCauchyLimit.JointJetLimit Us U := by
  obtain ⟨Us,U,hUs,hzero,hU,hLimit⟩ := exists_canonical_cutoff_positive_limit X μ hμ o χ hχ A hA B hb
  have hPDE := LocalCauchyLimit.formHeatEquation_limit X.metric μ hμ Us U
    (fun j => (hUs j).2.1) hU hLimit (fun j => (hUs j).2.2.1)
  have hInit := InitialTrace.formSmoothInitial_of_jointJetLimit_remoteBounds
    (CutoffTail.cutoffForm χ A) A Us U hA hzero (fun j _ => (hUs j).2.1) hU
    (fun j _ => canonicalCutoff_smoothInitial X.metric μ hμ o χ hχ A hA Us hUs j)
    hLimit (canonicalCutoff_remoteJetBounds X μ hμ o χ hχ A hA B hb Us hUs)
  exact ⟨Us,U,hUs,hzero,hU,hPDE,hInit,hLimit⟩

/-- No global L² condition is imposed on the bounded smooth initial form or
on its limit. Every original cutoff and every original L² heat family has
the same full local space-time C∞ limit, with the full original initial trace. -/
theorem exists_form_cutoff_limit {n : ℕ} (X : KahlerManifold n)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    (A : RealForm X.manifold 2) (hA : SmoothRealForm A)
    (B : ℝ) (hb : ∀ x, formNormSq X.metric.form A x ≤ B^2) :
    ∃ U : ℝ → RealForm X.manifold 2, U 0=A ∧ SmoothFormTime U (Set.Ioi 0) ∧
      FormHeatEquation X.metric.form U ∧ FormSmoothInitial U A ∧
      ∀ o χ, MetricCutoffFamily X.metric.form o χ →
        ∀ Vs : ℕ → ℝ → RealForm X.manifold 2,
          (∀ j, 1 ≤ j → IsL2FormHeat X.metric.form μ (fun x => χ j x • A x) (Vs j)) →
          FormHeatLocalSmoothLimit Vs U := by
  classical
  let o : Pt X := Classical.arbitrary _
  obtain ⟨χ,hχ⟩ := metricCutoffFamily X.metric o
  obtain ⟨Us,U,hUs,hzero,hU,hPDE,hInit,hLimit⟩ :=
    exists_canonical_cutoff_heat_initial X μ hμ o χ hχ A hA B hb
  refine ⟨U,hzero,hU,hPDE,hInit,?_⟩
  intro o' χ' hχ' Vs hVs
  exact original_cutoff_jointJetLimit X μ hμ o χ hχ A hA B hb Us hUs U hU hLimit o' χ' hχ' Vs hVs

end Yau.NodeProofs.P06Aux.CylinderReg
