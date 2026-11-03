import Yau.Proofs.F01SpaceTimeCommutation

/-! Actual complex spatial derivatives commute with the time derivative
on the open space-time chart; both sides use the original derivative operators. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace Yau.NodeProofs.F01Aux
open Yau
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem spatial_direction_time_differentiable (F : E × ℝ → ℂ)
    {S : Set E} {I : Set ℝ} (hS : IsOpen S) (hI : IsOpen I)
    (hF : ContDiffOn ℝ ∞ F (S ×ˢ I)) {x : E} {t : ℝ}
    (hx : x ∈ S) (ht : t ∈ I) (v : E) :
    DifferentiableAt ℝ (fun s => fderiv ℝ (fun y => F (y, s)) x v) t := by
  have hU : IsOpen (S ×ˢ I) := hS.prod hI
  have hAt : ContDiffAt ℝ ∞ F (x, t) := hF.contDiffAt (hU.mem_nhds ⟨hx, ht⟩)
  have hD : ContDiffAt ℝ 1 (fderiv ℝ F) (x, t) := hAt.fderiv_right (m := 1) (by simp)
  have hG : DifferentiableAt ℝ (fun p => fderiv ℝ F p (v, 0)) (x, t) :=
    hD.differentiableAt one_ne_zero |>.clm_apply (differentiableAt_const (v, 0))
  have hh := hG.comp t ((differentiableAt_const x).prodMk differentiableAt_id)
  apply hh.congr_of_eventuallyEq
  filter_upwards [hI.mem_nhds ht] with s hs
  exact fderiv_space_eq_product_fderiv F x s
    ((hF.contDiffAt (hU.mem_nhds ⟨hx, hs⟩)).differentiableAt (by simp)) v

theorem wirt_time_derivative_commute (F : E × ℝ → ℂ)
    {S : Set E} {I : Set ℝ} (hS : IsOpen S) (hI : IsOpen I)
    (hF : ContDiffOn ℝ ∞ F (S ×ˢ I)) {x : E} {t : ℝ}
    (hx : x ∈ S) (ht : t ∈ I) (v : E) :
    wirt (fun y => deriv (fun s => F (y, s)) t) x v =
      deriv (fun s => wirt (fun y => F (y, s)) x v) t := by
  have hA := spatial_direction_time_differentiable F hS hI hF hx ht v
  have hB := spatial_direction_time_differentiable F hS hI hF hx ht (Complex.I • v)
  unfold wirt
  rw [time_space_derivative_commute F hS hI hF hx ht v,
    time_space_derivative_commute F hS hI hF hx ht (Complex.I • v)]
  exact (((hA.hasDerivAt).sub ((hB.hasDerivAt).const_mul Complex.I)).const_mul
    (1 / 2 : ℂ)).deriv.symm

theorem wirtBar_time_derivative_commute (F : E × ℝ → ℂ)
    {S : Set E} {I : Set ℝ} (hS : IsOpen S) (hI : IsOpen I)
    (hF : ContDiffOn ℝ ∞ F (S ×ˢ I)) {x : E} {t : ℝ}
    (hx : x ∈ S) (ht : t ∈ I) (v : E) :
    wirtBar (fun y => deriv (fun s => F (y, s)) t) x v =
      deriv (fun s => wirtBar (fun y => F (y, s)) x v) t := by
  have hA := spatial_direction_time_differentiable F hS hI hF hx ht v
  have hB := spatial_direction_time_differentiable F hS hI hF hx ht (Complex.I • v)
  unfold wirtBar
  rw [time_space_derivative_commute F hS hI hF hx ht v,
    time_space_derivative_commute F hS hI hF hx ht (Complex.I • v)]
  exact (((hA.hasDerivAt).add ((hB.hasDerivAt).const_mul Complex.I)).const_mul
    (1 / 2 : ℂ)).deriv.symm

end Yau.NodeProofs.F01Aux
