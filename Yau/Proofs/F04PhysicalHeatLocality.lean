import Yau.Proofs.F04Adjoint
import Yau.Blueprint.Stages

open Filter Set
open scoped Topology ContDiff Manifold
noncomputable section
namespace Yau.F04Proof
open Yau.Blueprint

/-- Physical heatOp is local on an open spatial region and ANY time set.
 The time derivative uses genuine within-set equality at closed faces;
 the spatial Laplacian uses the actual physical germ. -/
theorem physical_heatOp_congr_of_eqOn
    {n : ℕ} (X : KahlerManifold n) (h : Flow X) {W : Set (Pt X)} (hW : IsOpen W)
    {I : Set ℝ} {f g : STF X}
    (he : EqOn (fun p : Pt X × ℝ => f p.1 p.2) (fun p => g p.1 p.2) (W ×ˢ I))
    {x : Pt X} (hx : x ∈ W) {t : ℝ} (ht : t ∈ I) :
    heatOp h I f x t = heatOp h I g x t := by
  have hTime : derivWithin (f x) I t = derivWithin (g x) I t :=
    derivWithin_congr (fun s hs => he (show (x,s) ∈ W ×ˢ I from ⟨hx,hs⟩))
      (he (show (x,t) ∈ W ×ˢ I from ⟨hx,ht⟩))
  have hSpace : (fun y => f y t) =ᶠ[𝓝 x] (fun y => g y t) :=
    eventually_of_mem (hW.mem_nhds hx)
      (fun y hy => he (show (y,t) ∈ W ×ˢ I from ⟨hy,ht⟩))
  exact congrArg₂ (fun a b : ℝ => a-b) hTime (laplacian_congr_of_eventuallyEq (h t) hSpace)

end Yau.F04Proof
