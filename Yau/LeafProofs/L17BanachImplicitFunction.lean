import Yau.LeafProofs.L17BanachImplicitFunctionInverse
import Yau.LeafProofs.L17BanachImplicitFunctionDerivative

noncomputable section
open Set
open scoped Topology ContDiff
set_option maxHeartbeats 2000000

namespace Yau.LeafProofs.L17BanachImplicitFunctionAux
open ContinuousLinearMap Yau.LeafProofs.L17SmallTranslationAux

variable {E X Y : Type*}
    [instE : NormedAddCommGroup E] [instER : NormedSpace ℝ E]
    [instX : NormedAddCommGroup X] [instXR : NormedSpace ℝ X]
    [instY : NormedAddCommGroup Y] [instYR : NormedSpace ℝ Y]
    [instCompleteE : CompleteSpace E] [instCompleteX : CompleteSpace X]

/-- The parameter branch and source uniqueness follow from the actual slice
derivative.  No inverse, branch, or additional derivative is supplied. -/
theorem implicit_function_of_slice_derivative {G : E × X → Y} {s : Set (E × X)}
    (hs : IsOpen s) (hG : ContDiffOn ℝ ∞ G s) (u : X) (hu : (0,u) ∈ s)
    (hGu : G (0,u)=0) (B : X ≃L[ℝ] Y)
    (hSlice : HasFDerivAt (fun v => G (0,v)) (B : X →L[ℝ] Y) u) :
    ∃ (U : Set E) (V : E → X) (W : Set (E × X)),
      IsOpen U ∧ (0 : E) ∈ U ∧ IsOpen W ∧ (0,u) ∈ W ∧ W ⊆ s ∧
      ContDiffOn ℝ ∞ V U ∧ V 0=u ∧
      (∀ p ∈ U, (p,V p) ∈ W ∧ G (p,V p)=0) ∧
      (∀ p ∈ U, ∀ v, (p,v) ∈ W → G (p,v)=0 → v=V p) := by
  have hn : (∞ : ℕ∞ω) ≠ 0 := by simp
  let D : E × X →L[ℝ] Y := fderiv ℝ G (0,u)
  have hD : HasFDerivAt G D (0,u) :=
    ((hG.contDiffAt (hs.mem_nhds hu)).differentiableAt hn).hasFDerivAt
  let A : E →L[ℝ] Y := D.comp (inl ℝ E X)
  let C : (E × X) ≃L[ℝ] (E × Y) := blockTriangularEquiv A B
  have hMap : ContDiffOn ℝ ∞ (fun q : E × X => (q.1,G q)) s :=
    contDiff_fst.contDiffOn.prodMk hG
  have hMapD : HasFDerivAt (fun q : E × X => (q.1,G q))
      (C : E × X →L[ℝ] E × Y) (0,u) :=
    parameter_map_hasFDerivAt hD B hSlice
  obtain ⟨e,he,hea,hes,hInv⟩ := smooth_inverse_on_open hs hMap hu C hMapD
  let U : Set E := {p | (p,(0 : Y)) ∈ e.target}
  let V : E → X := fun p => (e.symm (p,0)).2
  have hU : IsOpen U := e.open_target.preimage (continuous_id.prodMk continuous_const)
  have hBase : e (0,u)=(0,0) := by rw [he]; exact Prod.ext rfl hGu
  have h0 : (0 : E) ∈ U := by
    change (0,0) ∈ e.target
    rw [← hBase]
    exact e.map_source hea
  have hBaseInv : e.symm (0,0)=(0,u) := by rw [← hBase]; exact e.left_inv hea
  have hEmbed : ContDiffOn ℝ ∞ (fun p : E => (p,(0 : Y))) U :=
    contDiff_id.contDiffOn.prodMk contDiff_const.contDiffOn
  have hBranch : ContDiffOn ℝ ∞ (fun p : E => e.symm (p,0)) U :=
    hInv.comp hEmbed (fun _ hp => hp)
  have hV : ContDiffOn ℝ ∞ V U := hBranch.snd
  refine ⟨U,V,e.source,hU,h0,e.open_source,hea,hes,hV,?_,?_,?_⟩
  · change (e.symm (0,0)).2=u
    rw [hBaseInv]
  · intro p hp
    have hR := e.right_inv hp
    rw [he] at hR
    have hFirst : (e.symm (p,0)).1=p := congrArg (fun r : E × Y => r.1) hR
    have hEq : e.symm (p,0)=(p,V p) := Prod.ext hFirst rfl
    refine ⟨?_,?_⟩
    · rw [← hEq]
      exact e.map_target hp
    · have hSecond := congrArg (fun r : E × Y => r.2) hR
      rw [hEq] at hSecond
      exact hSecond
  · intro p hp v hv hZero
    have hEF : e (p,v)=(p,0) := by rw [he]; exact Prod.ext rfl hZero
    have hL := e.left_inv hv
    rw [hEF] at hL
    exact (congrArg (fun r : E × X => r.2) hL).symm

end Yau.LeafProofs.L17BanachImplicitFunctionAux
