import Yau.Proofs.F01MixedWirtingerLinearity

/-! Full product calculus for the actual nested mixed Wirtinger derivative. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs

theorem wirt_add_rule {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f g : E → ℂ) (z v : E) (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    wirt (fun y => f y + g y) z v = wirt f z v + wirt g z v := by
  unfold wirt
  rw [fderiv_fun_add hf hg]
  simp only [ContinuousLinearMap.add_apply]
  ring

theorem mixed_wirt_mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f g : E → ℂ) {S : Set E} (hS : IsOpen S)
    (hf : ContDiffOn ℝ ∞ f S) (hg : ContDiffOn ℝ ∞ g S)
    {z : E} (hz : z ∈ S) (v w : E) :
    wirt (fun y => wirtBar (fun u => f u * g u) y v) z w =
      wirt (fun y => wirtBar f y v) z w * g z +
      wirtBar f z v * wirt g z w + wirt f z w * wirtBar g z v +
      f z * wirt (fun y => wirtBar g y v) z w := by
  have hfd := (hf.contDiffAt (hS.mem_nhds hz)).differentiableAt (by simp)
  have hgd := (hg.contDiffAt (hS.mem_nhds hz)).differentiableAt (by simp)
  have hfb := ((L14Aux.wirtBar_contDiffOn hS f hf v).contDiffAt
    (hS.mem_nhds hz)).differentiableAt (by simp)
  have hgb := ((L14Aux.wirtBar_contDiffOn hS g hg v).contDiffAt
    (hS.mem_nhds hz)).differentiableAt (by simp)
  have heq : (fun y => wirtBar (fun u => f u * g u) y v) =ᶠ[𝓝 z]
      (fun y => wirtBar f y v * g y + f y * wirtBar g y v) := by
    filter_upwards [hS.mem_nhds hz] with y hy
    exact L14Aux.wirtBar_mul_rule f g y v
      ((hf.contDiffAt (hS.mem_nhds hy)).differentiableAt (by simp))
      ((hg.contDiffAt (hS.mem_nhds hy)).differentiableAt (by simp))
  rw [wirt_eq_of_eventuallyEq heq,
    wirt_add_rule (fun y : E => wirtBar f y v * g y)
      (fun y : E => f y * wirtBar g y v) z w (hfb.mul hgd) (hfd.mul hgb),
    L14Aux.wirt_mul_rule (fun y : E => wirtBar f y v) g z w hfb hgd,
    L14Aux.wirt_mul_rule f (fun y : E => wirtBar g y v) z w hfd hgb]
  ring

end Yau.NodeProofs.F01Aux
