import Yau.Proofs.P06HodgeRegularityLocalForms

/-! An arbitrary original strong Hodge heat path admits a single actual
dependent-form realization that is jointly smooth at every positive time. -/
noncomputable section
open MeasureTheory Filter Module
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux
open Yau Yau.LeafProofs Yau.LeafProofs.L03

variable {n k : ℕ} {M : ComplexManifold n}

theorem hodgeStrongPath_exists_joint_smooth_realization
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (h : ℝ → L2FormHilbert g μ k)
    (hheat : ∀ t, 0 < t → ∃ w, HasDerivAt h w t ∧
      (h t,(-2 : ℝ) • w) ∈ (hodgeCoreOperator g μ hμ k).closure.graph) :
    ∃ U : ℝ → RealForm M k, SmoothFormTime U (Set.Ioi 0) ∧
      ∀ t, 0 < t → ∃ hUt : L2RealForm g.form μ (U t), realizeActualForm g μ (U t) hUt = h t := by
  classical
  choose A hA hAr using fun t => l2FormHilbert_exists_section g μ (h t)
  have hlocal (x : M.Carrier) := hodgeStrongPath_exists_local_forms g μ hμ h hheat A
    (fun t _ => hA t) (fun t _ => hAr t) x
  choose N B hN hNx hB hBAE hBtime using hlocal
  obtain ⟨U,hU,hUAE,_⟩ := regularityLocalForms_glue g μ hμ A N hN hNx B hB hBAE hBtime
  refine ⟨U,hU,?_⟩
  intro t ht
  have hAE := hUAE t ht
  have hUt : L2RealForm g.form μ (U t) :=
    l2RealForm_of_ae_eq g.form (hAE.mono fun y hy => hy.symm) (hA t)
  refine ⟨hUt,?_⟩
  have hr : realizeActualForm g μ (U t) hUt = realizeActualForm g μ (A t) (hA t) :=
    (realizeL2Form_eq_iff_ae g μ (L2FormSpace.ofSection (U t) hUt) (L2FormSpace.ofSection (A t) (hA t))).mpr hAE
  exact hr.trans (hAr t)

end Yau.NodeProofs.P06Aux
