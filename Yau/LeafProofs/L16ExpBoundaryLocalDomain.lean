import Yau.LeafProofs.L16ExpBoundaryGeometry
import Yau.LeafProofs.L16ExpBoundaryComparison

open Filter Set
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius

noncomputable section

namespace Yau.LeafProofs.L16ExpBoundaryAux

open Yau.Parabolic Yau.ParabolicCandidates

theorem closure_inter_ball_subset {n : ℕ} (O : Set (Space n)) (y : Space n) (r : ℝ) :
    closure (O ∩ Metric.ball y r) ⊆ closure O ∩ Metric.closedBall y r := by
  intro x hx
  exact ⟨closure_mono inter_subset_left hx,
    Metric.closure_ball_subset_closedBall (closure_mono inter_subset_right hx)⟩

theorem frontier_inter_ball_cases {n : ℕ} {O : Set (Space n)} (hO : IsOpen O)
    {y x : Space n} {r : ℝ} (hx : x ∈ frontier (O ∩ Metric.ball y r)) :
    x ∈ frontier O ∨ (x ∈ closure O ∧ ‖x-y‖ = r) := by
  have hcl := closure_inter_ball_subset O y r hx.1
  by_cases hxO : x ∈ O
  · right
    have hn : x ∉ Metric.ball y r := by
      intro hb
      exact hx.2 (by simpa only [(hO.inter Metric.isOpen_ball).interior_eq,Set.mem_inter_iff]
        using And.intro hxO hb)
    have hge : r ≤ ‖x-y‖ := by
      simpa only [Metric.mem_ball,dist_eq_norm,not_lt] using hn
    have hle : ‖x-y‖ ≤ r := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hcl.2
    exact ⟨hcl.1,le_antisymm hle hge⟩
  · left
    exact ⟨hcl.1,by simpa only [hO.interior_eq] using hxO⟩

theorem nearby_closedBall_in_chart {n : ℕ} {x y : Space n} {R : ℝ}
    (hR : 0 < R) (hy : y ∈ Metric.ball x (R/4)) :
    Metric.closedBall y (R/4) ⊆ Metric.ball x R := by
  intro z hz
  have hdist := dist_triangle z y x
  have hzy : dist z y ≤ R/4 := hz
  have hyx : dist y x < R/4 := hy
  change dist z x < R
  linarith

theorem definingFunction_nearby_linear_bound {n : ℕ} {x y z : Space n}
    {R M₁ : ℝ} {s : Space n → ℝ} (hR : 0 < R)
    (hy : y ∈ Metric.ball x (R/4)) (hz : z ∈ Metric.closedBall y (R/4))
    (hs : ∀ p ∈ Metric.ball x R, DifferentiableAt ℝ s p)
    (hBound : ∀ p ∈ Metric.ball x R, ‖fderiv ℝ s p‖ ≤ M₁)
    (hzero : s y = 0) : s z ≤ M₁*‖z-y‖ := by
  have hyR : y ∈ Metric.ball x R := Metric.ball_subset_ball (by linarith) hy
  have hzR := nearby_closedBall_in_chart hR hy hz
  have hLip := (convex_ball x R).norm_image_sub_le_of_norm_fderiv_le hs hBound hyR hzR
  have hAbs : |s z| ≤ M₁*‖z-y‖ := by simpa only [hzero,sub_zero,Real.norm_eq_abs] using hLip
  exact (le_abs_self _).trans hAbs

/-- The time fiber is identical for any two closed spatial domains containing
the evaluation point, so restricting the spatial cylinder changes no operator. -/
theorem linearOp_closed_domain_eq {n : ℕ} {O D : Set (Space n)} {T : ℝ}
    {z : Point n} (hzO : z.1 ∈ closure O) (hzD : z.1 ∈ closure D)
    (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ) (u : Point n → ℝ) :
    linearOp (cylinder (closure D) 0 T) a b u z =
      linearOp (cylinder (closure O) 0 T) a b u z := by
  have hD : {t | (z.1,t) ∈ cylinder (closure D) 0 T} = Icc 0 T := by
    ext t
    simp [cylinder,hzD]
  have hO : {t | (z.1,t) ∈ cylinder (closure O) 0 T} = Icc 0 T := by
    ext t
    simp [cylinder,hzO]
  simp only [linearOp,timeD,hD,hO]

end Yau.LeafProofs.L16ExpBoundaryAux
