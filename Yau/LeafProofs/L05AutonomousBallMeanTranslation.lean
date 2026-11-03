import Yau.LeafProofs.L05AutonomousBallMeanLower

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic

theorem auto_ballMean_laplacian_translate {n : ℕ} (f : Space n → ℝ) (x y : Space n) :
    autoBallMeanLaplacian (fun z : Space n => f (x+z)) y=autoBallMeanLaplacian f (x+y) := by
  have hF : fderiv ℝ (fun z : Space n => f (x+z))=(fun z => fderiv ℝ f (x+z)) :=
    funext fun z => fderiv_comp_add_left x
  simp only [autoBallMeanLaplacian,hF,fderiv_comp_add_left]

theorem auto_ballMean_integral_translate {n : ℕ} (f : Space n → ℝ) (x : Space n) (r : ℝ) :
    (∫ y in ball (0 : Space n) r, f (x+y))=∫ y in ball x r, f y := by
  rw [← integral_indicator measurableSet_ball,← integral_indicator measurableSet_ball]
  have h := integral_add_left_eq_self (μ := volume) ((ball x r).indicator f) x
  convert h using 1
  congr 1
  funext y
  have hMem : x+y∈ball x r ↔ y∈ball (0 : Space n) r := by
    simp only [mem_ball,dist_eq_norm,add_sub_cancel_left,sub_zero]
  by_cases hy : y∈ball (0 : Space n) r
  · rw [indicator_of_mem hy,indicator_of_mem (hMem.mpr hy)]
  · rw [indicator_of_notMem hy,indicator_of_notMem (fun h => hy (hMem.mp h))]

theorem auto_ballMean_volume_translate (n : ℕ) (x : Space n) (r : ℝ) :
    (volume : Measure (Space n)).real (ball (0 : Space n) r)=(volume : Measure (Space n)).real (ball x r) := by
  have h := auto_ballMean_integral_translate (fun _ : Space n => (1 : ℝ)) x r
  simpa only [setIntegral_const,smul_eq_mul,mul_one] using h

theorem auto_ball_mean_lower {n : ℕ} (hn : 0 < n)
    {f : Space n → ℝ} {x : Space n} {r B : ℝ} (hr : 0 < r) (hB : 0 ≤ B)
    (_hf : ContDiffOn ℝ 2 f (closedBall x r))
    (hnear : ∀ y∈closedBall x r, ContDiffAt ℝ 2 f y)
    (hlap : ∀ y∈ball x r, -B ≤ ∑ i : Yau.RIdx n,
      (fderiv ℝ (fderiv ℝ f) y) (Yau.realVec i) (Yau.realVec i)) :
    (∫ y in ball x r, f y)/((volume : Measure (Space n)) (ball x r)).toReal-f x ≥
      -B*r^2/(2*((2*n : ℝ)+2)) := by
  have hnearG : ∀ y∈closedBall (0 : Space n) r, ContDiffAt ℝ 2 (fun z : Space n => f (x+z)) y := by
    intro y hy
    have hM : x+y∈closedBall x r := by
      simpa only [mem_closedBall,dist_eq_norm,add_sub_cancel_left,sub_zero] using hy
    exact (hnear (x+y) hM).comp y (contDiffAt_const.add contDiffAt_id)
  have hLapG : ∀ y∈ball (0 : Space n) r, -B ≤ autoBallMeanLaplacian (fun z : Space n => f (x+z)) y := by
    intro y hy
    rw [auto_ballMean_laplacian_translate]
    apply hlap
    simpa only [mem_ball,dist_eq_norm,add_sub_cancel_left,sub_zero] using hy
  have h := auto_ball_mean_lower_zero hn hr hB hnearG hLapG
  rw [auto_ballMean_integral_translate f x r,auto_ballMean_volume_translate n x r,add_zero] at h
  exact h

end Yau.LeafProofs.L05AutonomousAux
