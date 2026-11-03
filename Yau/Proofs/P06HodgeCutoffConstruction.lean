import Yau.Proofs.P06CylinderRegularity
import Yau.Proofs.P06BoundedCutoffLimits
import Yau.Proofs.P06CutoffHeatFamilies

noncomputable section
open MeasureTheory

namespace Yau.NodeProofs.P06Aux
open Yau Yau.Blueprint
variable {n : ℕ}

/-- The actual positive-time construction and its proved smooth initial
trace give the entire original cutoff target. Boundedness is derived from
the actual L² cutoff evolutions rather than assumed for the limit. -/
theorem hodgeCutoffConstruction (X : KahlerManifold n)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ) :
    HodgeCutoffConstruction X.metric.form μ := by
  classical
  constructor
  · exact metricCutoffFamily X.metric
  · intro A hA
    obtain ⟨B, _, hb⟩ := boundedOneOneData_global_norm X.metric.form A hA
    obtain ⟨U, _, hU, hPDE, hinit, hlimits⟩ :=
      CylinderReg.exists_form_cutoff_limit X μ hμ A hA.1 B hb
    let o : Pt X := Classical.arbitrary _
    obtain ⟨χ, hχ⟩ := metricCutoffFamily X.metric o
    obtain ⟨Us, hUs⟩ := metricCutoff_exists_l2Heat_family X.metric μ hμ A hA.1 o χ hχ
    have hbound := boundedFormHeatClass_of_metricCutoff_limit X μ hμ A hA o χ hχ Us U hUs
      (hlimits o χ hχ Us hUs)
    refine ⟨U, ⟨hU, hinit, hbound, hPDE⟩, ?_⟩
    intro o' χ' hχ'
    exact ⟨metricCutoff_smooth_l2 X.metric μ hμ o' χ' hχ' A hA.1,
      metricCutoff_exists_l2Heat_family X.metric μ hμ A hA.1 o' χ' hχ',
      hlimits o' χ' hχ'⟩

end Yau.NodeProofs.P06Aux

namespace Yau.NodeProofs
open Yau Yau.Blueprint

theorem P06_cutoff_construction_proved :
    ∀ (n : ℕ) (X : KahlerManifold n) (μ : Measure (Pt X)),
      IsRiemannianVolume X.metric.form μ → HodgeCutoffConstruction X.metric.form μ := by
  intro n X μ hμ
  exact P06Aux.hodgeCutoffConstruction X μ hμ

end Yau.NodeProofs
