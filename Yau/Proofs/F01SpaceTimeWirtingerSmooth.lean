import Yau.Proofs.F01WirtingerTimeCommutation
import Yau.Proofs.F01KahlerMixedExchange

/-! Full smoothness of the actual spatial Wirtinger jets in a fixed
space-time chart, and their genuine mixed time commutation. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace Yau.NodeProofs.F01Aux
open Yau
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def spaceTimeWirt (F : E × ℝ → ℂ) (v : E) (p : E × ℝ) : ℂ :=
  wirt (fun y => F (y, p.2)) p.1 v

def spaceTimeWirtBar (F : E × ℝ → ℂ) (v : E) (p : E × ℝ) : ℂ :=
  wirtBar (fun y => F (y, p.2)) p.1 v

theorem spaceTimeWirt_contDiffOn (F : E × ℝ → ℂ) (v : E)
    {U : Set (E × ℝ)} (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U) :
    ContDiffOn ℝ ∞ (spaceTimeWirt F v) U := by
  intro p hp
  have hD : ContDiffAt ℝ ∞ (fderiv ℝ F) p :=
    (hF.contDiffAt (hU.mem_nhds hp)).fderiv_right (m := ∞) (by simp)
  have hA : ContDiffAt ℝ ∞ (fun q => fderiv ℝ F q (v, 0)) p :=
    hD.clm_apply contDiffAt_const
  have hB : ContDiffAt ℝ ∞ (fun q => fderiv ℝ F q (Complex.I • v, 0)) p :=
    hD.clm_apply contDiffAt_const
  have hh : ContDiffAt ℝ ∞ (fun q => (1 / 2 : ℂ) *
      (fderiv ℝ F q (v, 0) - Complex.I * fderiv ℝ F q (Complex.I • v, 0))) p :=
    contDiffAt_const.mul (hA.sub (contDiffAt_const.mul hB))
  apply (hh.congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [hU.mem_nhds hp] with q hq
  have hd := (hF.contDiffAt (hU.mem_nhds hq)).differentiableAt (by simp)
  unfold spaceTimeWirt wirt
  rw [fderiv_space_eq_product_fderiv F q.1 q.2 hd v,
    fderiv_space_eq_product_fderiv F q.1 q.2 hd (Complex.I • v)]

theorem spaceTimeWirtBar_contDiffOn (F : E × ℝ → ℂ) (v : E)
    {U : Set (E × ℝ)} (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U) :
    ContDiffOn ℝ ∞ (spaceTimeWirtBar F v) U := by
  intro p hp
  have hD : ContDiffAt ℝ ∞ (fderiv ℝ F) p :=
    (hF.contDiffAt (hU.mem_nhds hp)).fderiv_right (m := ∞) (by simp)
  have hA : ContDiffAt ℝ ∞ (fun q => fderiv ℝ F q (v, 0)) p :=
    hD.clm_apply contDiffAt_const
  have hB : ContDiffAt ℝ ∞ (fun q => fderiv ℝ F q (Complex.I • v, 0)) p :=
    hD.clm_apply contDiffAt_const
  have hh : ContDiffAt ℝ ∞ (fun q => (1 / 2 : ℂ) *
      (fderiv ℝ F q (v, 0) + Complex.I * fderiv ℝ F q (Complex.I • v, 0))) p :=
    contDiffAt_const.mul (hA.add (contDiffAt_const.mul hB))
  apply (hh.congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [hU.mem_nhds hp] with q hq
  have hd := (hF.contDiffAt (hU.mem_nhds hq)).differentiableAt (by simp)
  unfold spaceTimeWirtBar wirtBar
  rw [fderiv_space_eq_product_fderiv F q.1 q.2 hd v,
    fderiv_space_eq_product_fderiv F q.1 q.2 hd (Complex.I • v)]

theorem mixed_wirtinger_time_derivative_commute (F : E × ℝ → ℂ)
    {S : Set E} {I : Set ℝ} (hS : IsOpen S) (hI : IsOpen I)
    (hF : ContDiffOn ℝ ∞ F (S ×ˢ I)) {x : E} {t : ℝ}
    (hx : x ∈ S) (ht : t ∈ I) (v w : E) :
    wirt (fun y => wirtBar (fun z => deriv (fun s => F (z, s)) t) y w) x v =
      deriv (fun s => wirt (fun y => wirtBar (fun z => F (z, s)) y w) x v) t := by
  have heq : (fun y => wirtBar (fun z => deriv (fun s => F (z, s)) t) y w) =ᶠ[𝓝 x]
      (fun y => deriv (fun s => spaceTimeWirtBar F w (y, s)) t) := by
    filter_upwards [hS.mem_nhds hx] with y hy
    exact wirtBar_time_derivative_commute F hS hI hF hy ht w
  rw [wirt_eq_of_eventuallyEq heq]
  exact wirt_time_derivative_commute (spaceTimeWirtBar F w) hS hI
    (spaceTimeWirtBar_contDiffOn F w (hS.prod hI) hF) hx ht v

end Yau.NodeProofs.F01Aux
