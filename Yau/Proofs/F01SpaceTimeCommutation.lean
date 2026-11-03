import Yau.Proofs.F01SpaceTimeDirections

/-! Genuine time/spatial derivative commutation for the actual smooth
scalar in a fixed open space-time chart. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace Yau.NodeProofs.F01Aux
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem time_space_derivative_commute (F : E × ℝ → ℂ)
    {S : Set E} {I : Set ℝ} (hS : IsOpen S) (hI : IsOpen I)
    (hF : ContDiffOn ℝ ∞ F (S ×ˢ I)) {x : E} {t : ℝ}
    (hx : x ∈ S) (ht : t ∈ I) (v : E) :
    fderiv ℝ (fun y => deriv (fun s => F (y, s)) t) x v =
      deriv (fun s => fderiv ℝ (fun y => F (y, s)) x v) t := by
  have hU : IsOpen (S ×ˢ I) := hS.prod hI
  have hAt : ContDiffAt ℝ ∞ F (x, t) := hF.contDiffAt (hU.mem_nhds ⟨hx, ht⟩)
  have hD : ContDiffAt ℝ 1 (fderiv ℝ F) (x, t) :=
    hAt.fderiv_right (m := 1) (by simp)
  have hG : DifferentiableAt ℝ (fun p => fderiv ℝ F p (0, 1)) (x, t) :=
    hD.differentiableAt one_ne_zero |>.clm_apply (differentiableAt_const (0, 1))
  have hH : DifferentiableAt ℝ (fun p => fderiv ℝ F p (v, 0)) (x, t) :=
    hD.differentiableAt one_ne_zero |>.clm_apply (differentiableAt_const (v, 0))
  have htime : (fun y => deriv (fun s => F (y, s)) t) =ᶠ[𝓝 x]
      (fun y => fderiv ℝ F (y, t) (0, 1)) := by
    filter_upwards [hS.mem_nhds hx] with y hy
    exact deriv_time_eq_product_fderiv F y t
      ((hF.contDiffAt (hU.mem_nhds ⟨hy, ht⟩)).differentiableAt (by simp))
  have hspace : (fun s => fderiv ℝ (fun y => F (y, s)) x v) =ᶠ[𝓝 t]
      (fun s => fderiv ℝ F (x, s) (v, 0)) := by
    filter_upwards [hI.mem_nhds ht] with s hs
    exact fderiv_space_eq_product_fderiv F x s
      ((hF.contDiffAt (hU.mem_nhds ⟨hx, hs⟩)).differentiableAt (by simp)) v
  rw [htime.fderiv_eq, hspace.deriv_eq,
    fderiv_space_eq_product_fderiv _ x t hG,
    deriv_time_eq_product_fderiv _ x t hH]
  exact product_directional_schwarz F x t (hAt.of_le (by simp)) v

end Yau.NodeProofs.F01Aux
