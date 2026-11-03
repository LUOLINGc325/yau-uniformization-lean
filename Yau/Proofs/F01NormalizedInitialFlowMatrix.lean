import Yau.Proofs.F01ParabolicDilationLevi
import Yau.Proofs.F01ClampedFlowMatrix
import Yau.Proofs.F01BackgroundInitialHolder

/-! In the actual bounded-geometry charts the normalized initial-surface
transformed matrix is the same native flow metric at the dilated clamped
time, with no replacement matrix field or Hessian-range oracle. -/
noncomputable section
open Set Metric
open scoped ContDiff Manifold Matrix ComplexOrder
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem normalized_initial_transformed_flow_matrix
    (α : HermitianField M) (hα : MetricSmooth α) (A : BoundedChartFamily α)
    (h : ℝ → HermitianField M) (U : M.Carrier → ℝ → ℝ) {T ρ : ℝ}
    (hρ : 0 < ρ) (hρr : ρ ≤ A.radius) (hρT : ρ ^ 2 ≤ T)
    (hU : SmoothSpaceTime U (Icc 0 T)) (hh0 : h 0 = α)
    (hpot : ∀ s ∈ Icc 0 T, ∀ x,
      gMat (h s) x = gMat α x - (s : ℂ) • ricci α x + levi (fun y => U y s) x)
    (a : M.Carrier) {p : Point n} (hp : p ∈ ball 0 1 ×ˢ Icc (-1) 1) :
    clampedBackground (fun z => pullbackMatrix α (A.chart a) (ρ • z)) p +
      complexHessianMap (hessian (forwardZeroSpaceTime
        (parabolicRescalePotential ρ (fun q : Point n => U (A.chart a q.1) q.2))) p) =
      iota (pullbackMatrix (h (ρ ^ 2 * max p.2 0)) (A.chart a) (ρ • p.1)) := by
  have he := A.differentiable a
  have hei := A.inverse_differentiable a
  have hsource : ball (0 : Space n) A.radius ⊆ (A.chart a).source :=
    fun z hz => A.closedBall_source a (ball_subset_closedBall hz)
  have hF : ContDiffOn ℝ ∞ (fun q : Point n => U (A.chart a q.1) q.2)
      (ball 0 A.radius ×ˢ Icc 0 T) :=
    (smoothSpaceTime_holomorphic_chart hU (A.chart a) he).mono
      (prod_mono hsource Subset.rfl)
  have hz := spatialDilation_mem_ball hρ hρr hp.1
  have hLog : ContDiffAt ℝ 2 (fun z => Real.log (pullbackMatrix α (A.chart a) z).det.re)
      (ρ • p.1) :=
    ((A.backgroundLogDet_smooth a).contDiffAt (isOpen_ball.mem_nhds hz)).of_le (by simp)
  rw [parabolicRescalePotential_clamped_matrix (pullbackMatrix α (A.chart a))
    hρ hρr hρT hF hp hLog]
  by_cases ht : p.2 ≤ 0
  · rw [if_pos ht, max_eq_right ht, mul_zero, hh0]
  · rw [if_neg ht, max_eq_left (lt_of_not_ge ht).le]
    have htime : ρ ^ 2 * p.2 ∈ Icc 0 T :=
      ⟨mul_nonneg (sq_nonneg _) (lt_of_not_ge ht).le,
        (mul_le_of_le_one_right (sq_nonneg ρ) hp.2.2).trans hρT⟩
    congr 1
    exact (flow_potential_matrix_in_chart α (h (ρ ^ 2 * p.2)) hα
      (fun x => U x (ρ ^ 2 * p.2)) (smoothSpaceTime_slice hU htime)
      (ρ ^ 2 * p.2) (hpot _ htime) (A.chart a) he hei (hsource hz)).symm

end Yau.NodeProofs.F01Aux
