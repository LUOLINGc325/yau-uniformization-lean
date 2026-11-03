import Yau.LeafProofs.L17SmallTranslationBlock
import Mathlib.Analysis.Calculus.FDeriv.Prod

noncomputable section
set_option maxHeartbeats 1600000

namespace Yau.LeafProofs.L17BanachImplicitFunctionAux
open ContinuousLinearMap Yau.LeafProofs.L17SmallTranslationAux

variable {E X Y : Type*}
    [instE : NormedAddCommGroup E] [instER : NormedSpace ℝ E]
    [instX : NormedAddCommGroup X] [instXR : NormedSpace ℝ X]
    [instY : NormedAddCommGroup Y] [instYR : NormedSpace ℝ Y]

/-- The actual slice derivative identifies the second column of the full
derivative, and hence the genuine block derivative of the parameter map. -/
theorem parameter_map_hasFDerivAt {G : E × X → Y} {q : E × X}
    {D : E × X →L[ℝ] Y} (hD : HasFDerivAt G D q) (B : X ≃L[ℝ] Y)
    (hSlice : HasFDerivAt (fun v => G (q.1,v)) (B : X →L[ℝ] Y) q.2) :
    HasFDerivAt (fun r : E × X => (r.1,G r))
      (blockTriangularEquiv (D.comp (inl ℝ E X)) B : E × X →L[ℝ] E × Y) q := by
  have hSliceD : HasFDerivAt (fun v => G (q.1,v)) (D.comp (inr ℝ E X)) q.2 :=
    hD.comp q.2 (hasFDerivAt_prodMk_right q.1 q.2)
  have hDB : D.comp (inr ℝ E X)=(B : X →L[ℝ] Y) := hSliceD.unique hSlice
  have hColumn (v : X) : D (0,v)=B v := by
    have h := congrArg (fun T : X →L[ℝ] Y => T v) hDB
    simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.inr_apply,
      ContinuousLinearEquiv.coe_apply] using h
  have hDecomp (p : E) (v : X) : D (p,v)=D (p,0)+B v := by
    calc
      D (p,v)=D ((p,0)+(0,v)) := by simp
      _=D (p,0)+D (0,v) := D.map_add _ _
      _=D (p,0)+B v := by rw [hColumn]
  have hBlock : (fst ℝ E X).prod D=
      (blockTriangularEquiv (D.comp (inl ℝ E X)) B : E × X →L[ℝ] E × Y) := by
    apply ContinuousLinearMap.ext
    intro r
    apply Prod.ext
    · rfl
    · exact hDecomp r.1 r.2
  rw [← hBlock]
  exact (hasFDerivAt_fst (𝕜 := ℝ)).prodMk hD

end Yau.LeafProofs.L17BanachImplicitFunctionAux
