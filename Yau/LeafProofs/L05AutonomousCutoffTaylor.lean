import Yau.LeafProofs.L05AutonomousAveragePairing
import Mathlib.Analysis.Calculus.MeanValue

noncomputable section
open Filter Set MeasureTheory Matrix
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic Yau.LeafProofs.L05Aux

local instance autoCutoffTaylor_dualGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] ℝ) := inferInstance
local instance autoCutoffTaylor_dualSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] ℝ) := inferInstance

/-- Two actual mean-value estimates give a quadratic remainder, including zero displacement. -/
theorem auto_global_taylor_remainder {n : ℕ} {f : Space n → ℝ} (hf : ContDiff ℝ 2 f)
    {B : ℝ} (hB : 0≤ B) (hbound : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖≤ B)
    (x h : Space n) : |f (x+h)-f x-fderiv ℝ f x h|≤ B*‖h‖^2 := by
  let D : Space n →L[ℝ] ℝ := fderiv ℝ f x
  let g : Space n → ℝ := fun z => f z-D z
  have hfD : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hgrad (z : Space n) : ‖fderiv ℝ f z-D‖≤ B*‖z-x‖ := by
    exact Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => hfD z) (fun z _ => hbound z) (convex_univ : Convex ℝ (univ : Set (Space n)))
        (mem_univ x) (mem_univ z)
  have hg (z : Space n) : DifferentiableAt ℝ g z :=
    (hf.differentiable (by norm_num) z).sub D.differentiableAt
  have hDg (z : Space n) : fderiv ℝ g z=fderiv ℝ f z-D := by
    simpa only [g,ContinuousLinearMap.fderiv] using
      fderiv_fun_sub (hf.differentiable (by norm_num) z) D.differentiableAt
  have hb (z : Space n) (hz : z∈Metric.closedBall x ‖h‖) : ‖fderiv ℝ g z‖≤ B*‖h‖ := by
    rw [hDg z]
    exact (hgrad z).trans (mul_le_mul_of_nonneg_left
      (by simpa only [Metric.mem_closedBall,dist_eq_norm] using hz) hB)
  have hx : x∈Metric.closedBall x ‖h‖ := Metric.mem_closedBall_self (norm_nonneg h)
  have hy : x+h∈Metric.closedBall x ‖h‖ := by simp only [Metric.mem_closedBall,dist_eq_norm,add_sub_cancel_left,le_refl]
  have hm := Convex.norm_image_sub_le_of_norm_fderiv_le (fun z _ => hg z) hb (convex_closedBall x ‖h‖) hx hy
  have heq : g (x+h)-g x=f (x+h)-f x-fderiv ℝ f x h := by
    dsimp only [g]
    rw [D.map_add]
    change f (x+h)-(D x+D h)-(f x-D x)=f (x+h)-f x-D h
    ring
  rw [heq,Real.norm_eq_abs,add_sub_cancel_left] at hm
  exact hm.trans_eq (by ring)

/-- A fixed compact smooth cutoff chooses its Hessian budget before every averaged source. -/
theorem auto_compact_taylor_budget {n : ℕ} {φ : Space n → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hcφ : HasCompactSupport φ) : ∃ C : ℝ, 0< C ∧
      ∀ x h : Space n, |φ (x+h)-φ x-fderiv ℝ φ x h|≤ C*‖h‖^2 := by
  have hcont : Continuous (fderiv ℝ (fderiv ℝ φ)) :=
    ((hφ.fderiv_right (m := 1) (by norm_num)).fderiv_right (m := 0) (by norm_num)).continuous
  obtain ⟨B,hB⟩ := hcont.bounded_above_of_compact_support ((hcφ.fderiv (𝕜 := ℝ)).fderiv (𝕜 := ℝ))
  let C := max B 0+1
  have hC : 0< C := by dsimp only [C];positivity
  have hBC : B≤ C := by dsimp only [C];linarith only [le_max_left B 0]
  exact ⟨C,hC,auto_global_taylor_remainder hφ hC.le (fun x => (hB x).trans hBC)⟩

end Yau.LeafProofs.L05AutonomousAux
