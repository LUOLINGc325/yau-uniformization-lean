import Yau.LeafProofs.L05AutonomousBallMeanAffine

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic Yau.LeafProofs.L05Aux Yau.ParabolicCandidates

theorem auto_ball_mean_square_root_transport {n : ℕ} (hn : 0 < n) {ell L : ℝ}
    (hell : 0 < ell) (hL : ell ≤ L) {A : Sym n} (hA : A∈slopeSet n ell L) :
    ∃ S : Space n ≃L[ℝ] Space n,
      ‖(S : Space n →L[ℝ] Space n)‖ ≤ Real.sqrt L ∧
      ‖(S.symm : Space n →L[ℝ] Space n)‖ ≤ (Real.sqrt ell)⁻¹ ∧
      (∀ H : Space n →L[ℝ] Space n →L[ℝ] ℝ,
        (∑ k : Yau.RIdx n, H (S (Yau.realVec k)) (S (Yau.realVec k)))=
          ∑ i, ∑ j, (A : Mat n) i j*H (Yau.realVec i) (Yau.realVec j)) ∧
      ∀ (f : Space n → ℝ) (x : Space n) (r R B : ℝ),
        0 < r → 0 ≤ B → Real.sqrt L*r ≤ R →
        (∀ z∈closedBall x R, ContDiffAt ℝ 2 f z) →
        (∀ z∈ball x R, -B ≤ ∑ i : Yau.RIdx n, ∑ j : Yau.RIdx n,
          (A : Mat n) i j*(fderiv ℝ (fderiv ℝ f) z) (Yau.realVec i) (Yau.realVec j)) →
        (∫ y in ball (0 : Space n) r, f (x+S y))/(volume : Measure (Space n)).real (ball 0 r)-f x ≥
          -B*r^2/(2*((2*n : ℝ)+2)) := by
  obtain ⟨S,hS,hSi,hST⟩ := auto_slope_space_equiv hell hL hA
  refine ⟨S,hS,hSi,hST,?_⟩
  intro f x r R B hr hB hBuffer hNear hTrace
  have hNorm (y : Space n) : ‖S y‖ ≤ Real.sqrt L*‖y‖ :=
    ((S : Space n →L[ℝ] Space n).le_opNorm y).trans (mul_le_mul_of_nonneg_right hS (norm_nonneg y))
  have hImage : ∀ y∈closedBall (0 : Space n) r, x+S y∈closedBall x R := by
    intro y hy
    have hY : ‖y‖ ≤ r := by simpa only [mem_closedBall,dist_zero_right] using hy
    have h := (hNorm y).trans ((mul_le_mul_of_nonneg_left hY (Real.sqrt_nonneg L)).trans hBuffer)
    simpa only [mem_closedBall,dist_eq_norm,add_sub_cancel_left] using h
  have hOpenImage : ∀ y∈ball (0 : Space n) r, x+S y∈ball x R := by
    intro y hy
    have hY : ‖y‖ < r := by simpa only [mem_ball,dist_zero_right] using hy
    have h := (hNorm y).trans_lt ((mul_lt_mul_of_pos_left hY (Real.sqrt_pos.mpr (hell.trans_le hL))).trans_le hBuffer)
    simpa only [mem_ball,dist_eq_norm,add_sub_cancel_left] using h
  have hNearG : ∀ y∈closedBall (0 : Space n) r, ContDiffAt ℝ 2 (fun z : Space n => f (x+S z)) y := by
    intro y hy
    exact (hNear (x+S y) (hImage y hy)).comp y (contDiffAt_const.add S.contDiff.contDiffAt)
  have hLapG : ∀ y∈ball (0 : Space n) r, -B ≤ autoBallMeanLaplacian (fun z : Space n => f (x+S z)) y := by
    intro y hy
    have hF := hNear (x+S y) (hImage y (ball_subset_closedBall hy))
    have hLap : autoBallMeanLaplacian (fun z : Space n => f (x+S z)) y=
        ∑ i : Yau.RIdx n, ∑ j : Yau.RIdx n,
          (A : Mat n) i j*(fderiv ℝ (fderiv ℝ f) (x+S y)) (Yau.realVec i) (Yau.realVec j) := by
      calc
        _ = ∑ k : Yau.RIdx n, (fderiv ℝ (fderiv ℝ f) (x+S y)) (S (Yau.realVec k)) (S (Yau.realVec k)) := by
          unfold autoBallMeanLaplacian
          apply Finset.sum_congr rfl
          intro k _
          exact auto_ballMean_affine_second (S : Space n →L[ℝ] Space n) x y hF (Yau.realVec k)
        _ = _ := hST _
    rw [hLap]
    exact hTrace _ (hOpenImage y hy)
  have h := auto_ball_mean_lower_zero hn hr hB hNearG hLapG
  simpa only [map_zero,add_zero] using h

end Yau.LeafProofs.L05AutonomousAux
