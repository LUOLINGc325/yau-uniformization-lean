import Yau.LeafProofs.L17LaplacianFinsum
import Yau.LeafProofs.L17GaussianParametrix

/-! Actual native regularity and Laplacian of the locally finite Gaussian sum. -/

open Set Metric Filter
open scoped Topology ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17Aux

open Yau.Parabolic L17HolderAux L17SchauderAux L17LocalizedSchauderAux L17ParabolicOperatorAux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

theorem gaussianLocal_contDiffOn_two (P : UniformChartPartition g) (T : ℝ) (hT : 0 ≤ T)
    {γ : ℝ} (f : HolderSpace P T γ) (p : P.centers)
    (hu : C2 (cylinder Set.univ 0 T) (localGaussian P T hT f p)) (t : Time T) :
    ContDiffOn ℝ 2 (fun z => gaussianLocalFunction P T hT f p (z,t))
      (ball (0 : Space n) (2*P.radius)) := by
  intro z _
  exact ((hu.2.2.2.2.1 (z,(t : ℝ)) ⟨mem_univ _,t.property⟩)).contDiffWithinAt

theorem gaussianTerm_native_contDiffAt (P : UniformChartPartition g) (T : ℝ) (hT : 0 ≤ T)
    {γ : ℝ} (f : HolderSpace P T γ) (p : P.centers)
    (hu : C2 (cylinder Set.univ 0 T) (localGaussian P T hT f p)) (x : M.Carrier) (t : Time T) :
    ContDiffAt ℝ 2 (inChart x (fun y => gaussianTerm P T hT f p (y,t))) (chartPt x x) := by
  obtain ⟨q,z,hzx⟩ := exists_selected_chart P x
  have hz : (z : Space n) ∈ (P.charts.chart q).source :=
    P.charts.closedBall_source q (ball_subset_closedBall ((ball_subset_ball P.radius_lt.le) z.property))
  have hBg := localizedTerm_chart_contDiffAt_two P T p q (gaussianLocalFunction P T hT f p) t
    (gaussianLocal_contDiffOn_two P T hT f p hu t) z.property
  have h := native_contDiffAt_of_background (P.charts.chart q) (P.charts.inverse_differentiable q)
    (fun y => gaussianTerm P T hT f p (y,t)) hz hBg
  simpa only [hzx] using h

theorem gaussianTerm_laplacian_zero_of_not_cover (P : UniformChartPartition g) (T : ℝ) (hT : 0 ≤ T)
    {γ : ℝ} (f : HolderSpace P T γ) (p : P.centers) (x : M.Carrier) (t : Time T)
    (hx : x ∉ P.charts.chart p '' closedBall 0 P.radius) :
    laplacian g (fun y => gaussianTerm P T hT f p (y,t)) x = 0 := by
  obtain ⟨q,z,hzx⟩ := exists_selected_chart P x
  have hz : (z : Space n) ∈ (P.charts.chart q).source :=
    P.charts.closedBall_source q (ball_subset_closedBall ((ball_subset_ball P.radius_lt.le) z.property))
  have hNear := localizedTerm_zero_neighborhood P T p (gaussianLocalFunction P T hT f p) hx
  have hChart : ContinuousAt (P.charts.chart q) z :=
    (P.charts.chart q).continuousOn.continuousAt ((P.charts.chart q).open_source.mem_nhds hz)
  rw [← hzx] at hNear ⊢
  apply laplacian_zero_of_background_zero (P.charts.chart q) (P.charts.differentiable q)
    (P.charts.inverse_differentiable q) _ hz
  filter_upwards [hChart.eventually hNear] with w hw
  exact hw t

theorem gaussianParametrixFun_laplacian (P : UniformChartPartition g) (T : ℝ) (hT : 0 ≤ T)
    {γ : ℝ} (f : HolderSpace P T γ)
    (hu : ∀ p, C2 (cylinder Set.univ 0 T) (localGaussian P T hT f p)) (x : M.Carrier) (t : Time T) :
    laplacian g (fun y => gaussianParametrixFun P T hT f (y,t)) x =
      ∑ᶠ p,laplacian g (fun y => gaussianTerm P T hT f p (y,t)) x := by
  obtain ⟨q,z,hzx⟩ := exists_selected_chart P x
  have hz : (z : Space n) ∈ (P.charts.chart q).source :=
    P.charts.closedBall_source q (ball_subset_closedBall ((ball_subset_ball P.radius_lt.le) z.property))
  obtain ⟨I,_,hNear⟩ := exists_active_neighborhood P x
  have hChart : ContinuousAt (P.charts.chart q) z :=
    (P.charts.chart q).continuousOn.continuousAt ((P.charts.chart q).open_source.mem_nhds hz)
  rw [← hzx] at hNear ⊢
  apply laplacian_finsum_background (P.charts.chart q) (P.charts.differentiable q)
    (P.charts.inverse_differentiable q) (fun p y => gaussianTerm P T hT f p (y,t)) I hz
  · intro p
    exact localizedTerm_chart_contDiffAt_two P T p q (gaussianLocalFunction P T hT f p) t
      (gaussianLocal_contDiffOn_two P T hT f p (hu p) t) z.property
  · filter_upwards [hChart.eventually hNear] with w hw p hp
    exact gaussianTerm_zero_of_not_cover P T hT f p _ (hw p hp)

end Yau.LeafProofs.L17Aux
