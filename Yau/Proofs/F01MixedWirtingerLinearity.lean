import Yau.Proofs.F01KahlerMixedExchange

/-! Linearity of the actual nested mixed operator on smooth coefficients. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs

theorem wirt_sub_rule {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f g : E → ℂ) (z v : E) (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    wirt (fun y => f y - g y) z v = wirt f z v - wirt g z v := by
  unfold wirt
  rw [fderiv_fun_sub hf hg]
  simp only [ContinuousLinearMap.sub_apply]
  ring

theorem mixed_wirt_sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f g : E → ℂ) {S : Set E} (hS : IsOpen S)
    (hf : ContDiffOn ℝ ∞ f S) (hg : ContDiffOn ℝ ∞ g S)
    {z : E} (hz : z ∈ S) (v w : E) :
    wirt (fun y => wirtBar (fun u => f u - g u) y v) z w =
      wirt (fun y => wirtBar f y v) z w - wirt (fun y => wirtBar g y v) z w := by
  have heq : (fun y => wirtBar (fun u => f u - g u) y v) =ᶠ[𝓝 z]
      (fun y => wirtBar f y v - wirtBar g y v) := by
    filter_upwards [hS.mem_nhds hz] with y hy
    exact L14Aux.wirtBar_sub_rule f g y v
      ((hf.contDiffAt (hS.mem_nhds hy)).differentiableAt (by simp))
      ((hg.contDiffAt (hS.mem_nhds hy)).differentiableAt (by simp))
  rw [wirt_eq_of_eventuallyEq heq]
  exact wirt_sub_rule _ _ z w
    (((L14Aux.wirtBar_contDiffOn hS f hf v).contDiffAt (hS.mem_nhds hz)).differentiableAt (by simp))
    (((L14Aux.wirtBar_contDiffOn hS g hg v).contDiffAt (hS.mem_nhds hz)).differentiableAt (by simp))

end Yau.NodeProofs.F01Aux
