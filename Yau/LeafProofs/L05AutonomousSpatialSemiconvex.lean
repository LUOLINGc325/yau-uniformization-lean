import Yau.LeafProofs.L05AutonomousSpatialConvex
import Yau.LeafProofs.L05AutonomousMollifiedHessianBounds

noncomputable section
open Filter Set MeasureTheory
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius BoundedContinuousFunction
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic Yau.LeafProofs.L05Aux

theorem auto_spatial_second_add {n : ℕ} {f g : Space n → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (x v : Space n) :
    fderiv ℝ (fderiv ℝ (fun y => f y+g y)) x v v=
      fderiv ℝ (fderiv ℝ f) x v v+fderiv ℝ (fderiv ℝ g) x v v := by
  have hFirst : fderiv ℝ (fun y => f y+g y)=fun y => fderiv ℝ f y+fderiv ℝ g y :=
    funext fun y => fderiv_fun_add (hf.differentiable (by simp) y) (hg.differentiable (by simp) y)
  rw [hFirst,fderiv_fun_add
    ((hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x)
    ((hg.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x)]
  rfl

theorem auto_smooth_spatial_semiconvex {n : ℕ} {O : Set (Space n)} (hO : Convex ℝ O)
    {f : Space n → ℝ} (hf : ContDiff ℝ ∞ f) (C : ℝ)
    (hLower : ∀ x∈O, ∀ v : Space n, -C*‖v‖^2 ≤ fderiv ℝ (fderiv ℝ f) x v v) :
    ConvexOn ℝ O (fun x => f x+(C/2)*‖x‖^2) := by
  have hq : ContDiff ℝ ∞ (fun x : Space n => (C/2)*‖x‖^2) := contDiff_const.mul (contDiff_norm_sq ℝ)
  apply auto_convexOn_of_spatial_second_nonneg hO (hf.add hq)
  intro x hx v
  rw [auto_spatial_second_add hf hq,auto_spatial_quadratic_second]
  linarith only [hLower x hx v]

/-- Actual smooth Hessian budgets and genuine uniform convergence yield semiconvex original slices. -/
theorem auto_uniform_spatial_semiconvex :
    ∀ n : ℕ, 0 < n → ∀ ell L : ℝ, 0 < ell → ell ≤ L →
    ∃ C : ℝ, 0 < C ∧
      ∀ F : Sym n → ℝ, Continuous F → globalElliptic F ell L → ConcaveOn ℝ univ F → F 0=0 →
      ∀ u : Point n → ℝ, ContinuousOn u (unitClosed n) → (∀ p∈unitClosed n, |u p|≤ 1) →
        viscositySolution (unitOpen n) (fun H _ => F H) (fun _ => 0) u →
        ∀ t∈Icc (-(5/8 : ℝ)^2) 0,
          ConvexOn ℝ (Metric.ball (0 : Space n) (5/8)) (fun x => u (x,t)+(C/2)*‖x‖^2) := by
  intro n hn ell L hell hL
  obtain ⟨B,hB,hForU⟩ := auto_uniform_mollified_hessian n hn ell L hell hL
  obtain ⟨D,hD,hDirection⟩ := auto_second_direction_budget n
  refine ⟨D*B,mul_pos hD hB,?_⟩
  intro F hF hE hConc h0 u hu hb hsol t ht
  obtain ⟨w,hwu,hw,hcw,hw1,hHessian⟩ := hForU F hF hE hConc h0 u hu hb hsol
  let eps := autoDyadicStep (1/512 : ℝ)
  have heps (j : ℕ) : 0 < eps j := auto_dyadicStep_pos (by norm_num) j
  have hepsSmall (j : ℕ) : eps j < 1/256 :=
    (auto_dyadicStep_le (by norm_num : (0 : ℝ) ≤ 1/512) j).trans_lt (by norm_num)
  have hConvex (j : ℕ) : ConvexOn ℝ (Metric.ball (0 : Space n) (5/8))
      (fun x => autoSpatialMollify (eps j) (heps j) w (x,t)+(D*B/2)*‖x‖^2) := by
    let f : Space n → ℝ := fun y => autoSpatialMollify (eps j) (heps j) w (y,t)
    have hf := autoSpatialMollify_spatial_contDiff (eps j) (heps j) w hw t
    apply auto_smooth_spatial_semiconvex (convex_ball _ _) hf (D*B)
    intro x hx v
    have hPoint : (x,t)∈autoClosed (0 : Space n) (45/64) 0 := by
      refine ⟨?_,?_⟩
      · have hxnorm : ‖x‖ < 5/8 := by simpa only [Metric.mem_ball,dist_zero_right] using hx
        simpa only [Metric.mem_closedBall,dist_zero_right] using hxnorm.le.trans (by norm_num : (5/8 : ℝ) ≤ 45/64)
      · change (0 : ℝ)-(45/64)^2 ≤ t ∧ t ≤ 0
        exact ⟨by linarith only [ht.1],ht.2⟩
    let H : Space n →L[ℝ] Space n →L[ℝ] ℝ := fderiv ℝ (fderiv ℝ f) x
    have hUpper (e : Space n) (he : ‖e‖=1) : (-H) e e ≤ D*B := by
      have hdir : |H e e| ≤ D*‖secondFDerivMatrix f x‖ := hDirection f x e he.le
      have hH : ‖secondFDerivMatrix f x‖ ≤ B := hHessian (eps j) (heps j) (hepsSmall j) (x,t) hPoint
      have hh : |H e e| ≤ D*B := hdir.trans (mul_le_mul_of_nonneg_left hH hD.le)
      change -(H e e) ≤ D*B
      exact (neg_le_abs _).trans hh
    have hh : -(H v v) ≤ D*B*‖v‖^2 := by
      simpa only [ContinuousLinearMap.neg_apply] using auto_bilinear_upper_homogeneous (-H) hUpper v
    change -(D*B)*‖v‖^2 ≤ H v v
    linarith only [hh]
  have hUniform := autoSpatialMollify_uniform w hw eps heps (auto_dyadicStep_tendsto _)
  apply auto_convexOn_of_pointwise_limit hConvex
  intro x hx
  have hxnorm : ‖x‖ < 5/8 := by simpa only [Metric.mem_ball,dist_zero_right] using hx
  have hPoint : (x,t)∈unitClosed n :=
    ⟨by simpa only [Metric.mem_closedBall,dist_zero_right] using hxnorm.le.trans (by norm_num : (5/8 : ℝ) ≤ 1),
      ⟨by linarith only [ht.1],ht.2⟩⟩
  have hlim := (hUniform.tendsto_at (x,t)).add_const ((D*B/2)*‖x‖^2)
  rwa [hwu hPoint] at hlim

end Yau.LeafProofs.L05AutonomousAux
