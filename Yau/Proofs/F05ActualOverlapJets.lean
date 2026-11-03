import Yau.Proofs.F05TransitionInverse
import Yau.Proofs.F05JetOperator
import Yau.LeafProofs.L16NonlinearChartCalculus

/-! The actual derivatives of one manifold function satisfy the precise
overlap identities, including the full second derivative of the transition. -/

open Set Filter
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types true
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_actual_overlap_jets {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) {T : ℝ} (w : M.Carrier → ℝ → ℝ)
    (hw : ∀ i : Fin A.count, C2 (F05Q A i T) (pull A i w)) (p : F05OverlapPoint A T) :
    pull A p.left w p.leftPoint.val = pull A p.right w p.rightPoint.val ∧
    timeD (F05Q A p.left T) (pull A p.left w) p.leftPoint.val =
      timeD (F05Q A p.right T) (pull A p.right w) p.rightPoint.val ∧
    spatialD (pull A p.left w) p.leftPoint.val =
      (spatialD (pull A p.right w) p.rightPoint.val).comp
        (fderiv ℝ (F05Transition A p.left p.right) p.leftCoord.val) ∧
    spatialDD (pull A p.left w) p.leftPoint.val =
      chartSecondJet (fderiv ℝ (F05Transition A p.left p.right) p.leftCoord.val)
        (fderiv ℝ (fderiv ℝ (F05Transition A p.left p.right)) p.leftCoord.val)
        (spatialD (pull A p.right w) p.rightPoint.val)
        (spatialDD (pull A p.right w) p.rightPoint.val) := by
  have hDomain : p.leftCoord.val ∈ F05TransitionDomain A p.left p.right :=
    ⟨F05D_mem_ball p.leftCoord.property,p.rightCoord.val,F05D_mem_ball p.rightCoord.property,p.samePoint.symm⟩
  have hNear := F05Transition_lift_near hA p.left p.right hDomain
  have hSlice : (fun z => pull A p.left w (z,p.time.val)) =ᶠ[𝓝 p.leftCoord.val]
      (fun z => chartSpaceTimePullback (F05Transition A p.left p.right)
        (pull A p.right w) (z,p.time.val)) := by
    filter_upwards [hNear] with z hz
    change w (lift A p.left z) p.time.val = w (lift A p.right (F05Transition A p.left p.right z)) p.time.val
    rw [hz]
  have hTransition := (F05Transition_overlap_contDiffAt hA p).of_le (by simp : (2 : ℕ∞ω) ≤ ∞)
  have hOuter : ContDiffAt ℝ 2 (fun z => pull A p.right w (z,p.time.val))
      (F05Transition A p.left p.right p.leftCoord.val) := by
    rw [F05Transition_overlap_value hA p]
    exact (hw p.right).2.2.2.2.1 p.rightPoint.val p.rightPoint.property
  have hG := spatialD_chartSpaceTimePullback p.leftPoint.val
    (hTransition.differentiableAt (by norm_num)) (hOuter.differentiableAt (by norm_num))
  have hH := spatialDD_chartSpaceTimePullback p.leftPoint.val hTransition hOuter
  have hG' : spatialD (pull A p.left w) p.leftPoint.val =
      spatialD (chartSpaceTimePullback (F05Transition A p.left p.right) (pull A p.right w)) p.leftPoint.val :=
    hSlice.fderiv_eq (𝕜 := ℝ)
  have hH' : spatialDD (pull A p.left w) p.leftPoint.val =
      spatialDD (chartSpaceTimePullback (F05Transition A p.left p.right) (pull A p.right w)) p.leftPoint.val :=
    (hSlice.fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)
  have hPoint : (F05Transition A p.left p.right p.leftCoord.val,p.time.val) = p.rightPoint.val := by
    exact Prod.ext (F05Transition_overlap_value hA p) rfl
  refine ⟨?_,?_,?_,?_⟩
  · change w (lift A p.left p.leftCoord.val) p.time.val = w (lift A p.right p.rightCoord.val) p.time.val
    rw [p.samePoint]
  · have hLeftTime := F05_timeD_pull A p.left T w (p := p.leftPoint.val) p.leftCoord.property
    have hRightTime := F05_timeD_pull A p.right T w (p := p.rightPoint.val) p.rightCoord.property
    calc
      _ = derivWithin (w (lift A p.left p.leftCoord.val)) (Icc 0 T) p.time.val := hLeftTime
      _ = derivWithin (w (lift A p.right p.rightCoord.val)) (Icc 0 T) p.time.val := by rw [p.samePoint]
      _ = _ := hRightTime.symm
  · rw [hG',hG]
    change (spatialD (pull A p.right w) (F05Transition A p.left p.right p.leftCoord.val,p.time.val)).comp _ = _
    rw [hPoint]
    rfl
  · rw [hH',hH]
    change chartSecondJet _ _
      (spatialD (pull A p.right w) (F05Transition A p.left p.right p.leftCoord.val,p.time.val))
      (spatialDD (pull A p.right w) (F05Transition A p.left p.right p.leftCoord.val,p.time.val)) = _
    rw [hPoint]
    rfl

end Yau.Proofs.F05Aux
