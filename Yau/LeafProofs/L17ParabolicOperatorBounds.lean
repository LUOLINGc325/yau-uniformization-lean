import Yau.LeafProofs.L17ParabolicOperatorRegularity

open Set Metric
open scoped Topology ContDiff Matrix.Norms.Elementwise
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17ParabolicOperatorAux
open Yau.LeafProofs.L17Aux Yau.LeafProofs.L17HolderAux Yau.LeafProofs.L17SchauderAux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
  {P : UniformChartPartition g} {T gamma : ℝ} {hT : 0 < T}

def laplacianBudget (A : BoundedChartFamily g) (gamma : ℝ) : ℝ :=
  1+contractionBudget n*coefficientBudget A*(1+(3 : ℝ)^(1-gamma))

theorem laplacianBudget_ge_one (A : BoundedChartFamily g) (gamma : ℝ) :
    1 ≤ laplacianBudget A gamma := by
  unfold laplacianBudget
  have hC := zero_le_one.trans (coefficientBudget_ge_one A)
  have hD := contractionBudget_nonneg n
  exact le_add_of_nonneg_right (mul_nonneg (mul_nonneg hD hC)
    (add_nonneg zero_le_one (Real.rpow_pos_of_pos (by norm_num) _).le))

theorem contraction_coefficient_le_laplacianBudget (A : BoundedChartFamily g) (gamma : ℝ) :
    contractionBudget n*coefficientBudget A ≤ laplacianBudget A gamma := by
  have hC := mul_nonneg (contractionBudget_nonneg n) (zero_le_one.trans (coefficientBudget_ge_one A))
  have hP := Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) (1-gamma)
  unfold laplacianBudget
  nlinarith only [hC,hP,mul_nonneg hC hP.le]

theorem actualLaplacian_point_bound (u : SchauderSpace P T gamma hT) (q : Cylinder M T) :
    |actualLaplacian u q| ≤ (contractionBudget n*coefficientBudget P.charts)*‖u‖ := by
  obtain ⟨p,z,hzx⟩ := exists_selected_chart P q.1
  have hz : (z : ComplexVector n) ∈ ball 0 P.charts.radius := (ball_subset_ball P.radius_lt.le) z.property
  have h := selected_chart_laplacian u p z q.2
  rw [hzx] at h
  change |laplacian g (fun y => schauderFun u (y,q.2)) q.1| ≤ _
  rw [h]
  have hb := hessianContractionCLM_bound (chartCoefficient P.charts p z) (hessianFun u ⟨p,(z,q.2)⟩)
  rw [Real.norm_eq_abs] at hb
  apply hb.trans
  exact mul_le_mul (mul_le_mul_of_nonneg_left (chartCoefficient_bounds P.charts p hz).1 (contractionBudget_nonneg n))
    ((hessian_holder_bounds u).1 _) (norm_nonneg _)
    (mul_nonneg (contractionBudget_nonneg n) (zero_le_one.trans (coefficientBudget_ge_one _)))

theorem actualLaplacian_weighted_bound (hTime : T ≤ P.radius^2) (hgamma : gamma ≤ 1)
    (hr : P.radius ≤ 1) (u : SchauderSpace P T gamma hT) (i : ChartPairs P T) :
    |pairWeight P T gamma i*(actualLaplacian u (chartRight P T i)-actualLaplacian u (chartLeft P T i))| ≤
      laplacianBudget P.charts gamma*‖u‖ := by
  have hD := contractionBudget_nonneg n
  have hC := zero_le_one.trans (coefficientBudget_ge_one P.charts)
  have hP := (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) (1-gamma)).le
  have hz : (i.2.val.2.1 : ComplexVector n) ∈ ball 0 P.charts.radius :=
    (ball_subset_ball P.radius_lt.le) i.2.val.2.1.property
  change |pairWeight P T gamma i*(
    laplacian g (fun y => schauderFun u (y,i.2.val.2.2)) (P.charts.chart i.1 i.2.val.2.1)-
    laplacian g (fun y => schauderFun u (y,i.2.val.1.2)) (P.charts.chart i.1 i.2.val.1.1))| ≤ _
  rw [selected_chart_laplacian u i.1 i.2.val.2.1 i.2.val.2.2,
    selected_chart_laplacian u i.1 i.2.val.1.1 i.2.val.1.2]
  change ‖pairWeight P T gamma i*(
    hessianContractionCLM n (chartCoefficient P.charts i.1 i.2.val.2.1) (hessianFun u (localRight P T i))-
    hessianContractionCLM n (chartCoefficient P.charts i.1 i.2.val.1.1) (hessianFun u (localLeft P T i)))‖ ≤ _
  rw [hessianContractionCLM_weighted_difference]
  calc
    _ ≤ ‖hessianContractionCLM n (chartCoefficient P.charts i.1 i.2.val.2.1)
        (pairWeight P T gamma i • (hessianFun u (localRight P T i)-hessianFun u (localLeft P T i)))‖+
      ‖hessianContractionCLM n (pairWeight P T gamma i •
        (chartCoefficient P.charts i.1 i.2.val.2.1-chartCoefficient P.charts i.1 i.2.val.1.1))
        (hessianFun u (localLeft P T i))‖ := norm_add_le _ _
    _ ≤ (contractionBudget n*coefficientBudget P.charts)*‖u‖+
        (contractionBudget n*(coefficientBudget P.charts*(3 : ℝ)^(1-gamma)))*‖u‖ := by
      apply add_le_add
      · apply (hessianContractionCLM_bound _ _).trans
        exact mul_le_mul (mul_le_mul_of_nonneg_left (chartCoefficient_bounds P.charts i.1 hz).1 hD)
          ((hessian_holder_bounds u).2 i) (norm_nonneg _) (mul_nonneg hD hC)
      · apply (hessianContractionCLM_bound _ _).trans
        exact mul_le_mul (mul_le_mul_of_nonneg_left (weighted_chartCoefficient_difference P hTime hgamma hr i) hD)
          ((hessian_holder_bounds u).1 _) (norm_nonneg _) (mul_nonneg hD (mul_nonneg hC hP))
    _ ≤ _ := by
      unfold laplacianBudget
      nlinarith only [norm_nonneg u]

theorem actualLaplacian_holder_bounds (hTime : T ≤ P.radius^2) (hgamma : gamma ≤ 1)
    (hr : P.radius ≤ 1) (u : SchauderSpace P T gamma hT) :
    (∀ q, |actualLaplacian u q| ≤ laplacianBudget P.charts gamma*‖u‖) ∧
    ∀ i : ChartPairs P T,
      |pairWeight P T gamma i*(actualLaplacian u (chartRight P T i)-actualLaplacian u (chartLeft P T i))| ≤
        laplacianBudget P.charts gamma*‖u‖ :=
  ⟨fun q => (actualLaplacian_point_bound u q).trans (mul_le_mul_of_nonneg_right
      (contraction_coefficient_le_laplacianBudget P.charts gamma) (norm_nonneg u)),
    actualLaplacian_weighted_bound hTime hgamma hr u⟩

end Yau.LeafProofs.L17ParabolicOperatorAux
