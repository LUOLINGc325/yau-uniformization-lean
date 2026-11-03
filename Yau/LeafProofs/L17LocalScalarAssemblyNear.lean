import Yau.LeafProofs.L17LocalScalarAssemblyContinuity
import Mathlib.Analysis.Calculus.MeanValue

open Set Metric
open scoped ContDiff
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17LocalScalarAssemblyAux
open L17Aux L17HolderAux L17SchauderAux L17LocalizedSchauderAux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

theorem local_value_difference_le (P : UniformChartPartition g) {T γ : ℝ}
    (u : LocalHolderSpace ℝ P T γ) (p : P.centers) (q r : ChartCylinder P T) :
    |localFun ℝ u ⟨p,q⟩-localFun ℝ u ⟨p,r⟩| ≤
      ‖u‖*(parabolicDistance q r/P.radius)^γ := by
  by_cases hqr : q=r
  · subst r
    simp only [sub_self,abs_zero,parabolicDistance,norm_zero,Real.sqrt_zero,zero_add,zero_div]
    positivity
  · let i : ChartPairs P T := ⟨p,⟨(q,r),hqr⟩⟩
    have h := localWeighted_difference_norm_le ℝ u i
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (pairWeight_pos P T γ i)] at h
    change pairWeight P T γ i*|localFun ℝ u ⟨p,r⟩-localFun ℝ u ⟨p,q⟩| ≤ ‖u‖ at h
    rw [abs_sub_comm] at h
    have hpow : 0 ≤ (parabolicDistance q r/P.radius)^γ :=
      Real.rpow_nonneg (div_nonneg (parabolicDistance_pos_of_ne hqr).le P.radius_pos.le) _
    calc
      |localFun ℝ u ⟨p,q⟩-localFun ℝ u ⟨p,r⟩| =
          (pairWeight P T γ i*|localFun ℝ u ⟨p,q⟩-localFun ℝ u ⟨p,r⟩|)*
            (parabolicDistance q r/P.radius)^γ := by
        rw [mul_right_comm,pairWeight_mul_scaled_power P T γ i,one_mul]
      _ ≤ ‖u‖*(parabolicDistance q r/P.radius)^γ := mul_le_mul_of_nonneg_right h hpow

theorem weight_chart_lipschitz (P : UniformChartPartition g) {Cw : ℝ}
    (hD : ∀ (p : P.centers) (q : M.Carrier) z, z ∈ ball (0 : ComplexVector n) (2*P.radius) →
      ‖fderiv ℝ (fun w => P.weight p (P.charts.chart q w)) z‖ ≤ Cw/P.radius)
    (p : P.centers) (z w : ↥(ball (0 : ComplexVector n) P.radius)) :
    |P.weight p (P.charts.chart p w)-P.weight p (P.charts.chart p z)| ≤
      (Cw/P.radius)*‖(w : ComplexVector n)-z‖ := by
  have hdiff : ∀ y ∈ ball (0 : ComplexVector n) P.radius,
      DifferentiableAt ℝ (fun v => P.weight p (P.charts.chart p v)) y := by
    intro y hy
    apply ((smoothFn_comp_backgroundChart_contDiffOn P.charts (P.weight_smooth p) p).contDiffAt
      (isOpen_ball.mem_nhds ((ball_subset_ball P.radius_lt.le) hy))).differentiableAt
    simp
  simpa only [Real.norm_eq_abs] using Convex.norm_image_sub_le_of_norm_fderiv_le
    hdiff (fun y hy => hD p p y ((ball_subset_ball (by linarith [P.radius_pos])) hy))
    (convex_ball (0 : ComplexVector n) P.radius) z.property w.property

theorem scaled_linear_le_holder {d γ : ℝ} (hd : 0 < d) (hd3 : d ≤ 3) (hγ : γ ≤ 1) :
    d ≤ (3 : ℝ)^(1-γ)*d^γ := by
  calc
    d = d^((1-γ)+γ) := by rw [sub_add_cancel,Real.rpow_one]
    _ = d^(1-γ)*d^γ := Real.rpow_add hd _ _
    _ ≤ (3 : ℝ)^(1-γ)*d^γ := mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow hd.le hd3 (sub_nonneg.mpr hγ)) (Real.rpow_nonneg hd.le _)

theorem weightedLocalFunction_difference_inside (P : UniformChartPartition g) {T γ Cw : ℝ}
    (hTime : T ≤ P.radius^2) (hγ : γ ≤ 1) (hCw : 0 ≤ Cw)
    (hD : ∀ (p : P.centers) (q : M.Carrier) z, z ∈ ball (0 : ComplexVector n) (2*P.radius) →
      ‖fderiv ℝ (fun w => P.weight p (P.charts.chart q w)) z‖ ≤ Cw/P.radius)
    (u : LocalHolderSpace ℝ P T γ) (p : P.centers) (q r : ChartCylinder P T) :
    |weightedLocalFunction P u p (q.1,q.2)-weightedLocalFunction P u p (r.1,r.2)| ≤
      ((1+Cw*(3 : ℝ)^(1-γ))*‖u‖)*(parabolicDistance q r/P.radius)^γ := by
  by_cases hqr : q=r
  · subst r
    rw [sub_self,abs_zero]
    simp only [parabolicDistance,sub_self,norm_zero,abs_zero,Real.sqrt_zero,zero_add,zero_div]
    exact mul_nonneg (mul_nonneg (by positivity) (norm_nonneg u))
      (Real.rpow_nonneg (by norm_num) _)
  · let d := parabolicDistance q r/P.radius
    have hd : 0 < d := div_pos (parabolicDistance_pos_of_ne hqr) P.radius_pos
    have hd3 : d ≤ 3 := (div_le_iff₀ P.radius_pos).mpr (parabolicDistance_le_three_radius P hTime q r)
    have hp : 0 ≤ d^γ := Real.rpow_nonneg hd.le _
    have hu := local_value_difference_le P u p q r
    have hv : |localFun ℝ u ⟨p,r⟩| ≤ ‖u‖ := by
      simpa only [Real.norm_eq_abs] using localValue_norm_le ℝ u ⟨p,r⟩
    have hw : |P.weight p (P.charts.chart p q.1)-P.weight p (P.charts.chart p r.1)| ≤ Cw*d := by
      apply (weight_chart_lipschitz P hD p r.1 q.1).trans
      calc
        (Cw/P.radius)*‖(q.1 : ComplexVector n)-r.1‖ ≤ (Cw/P.radius)*parabolicDistance q r :=
          mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (Real.sqrt_nonneg _))
            (div_nonneg hCw P.radius_pos.le)
        _ = Cw*d := by dsimp only [d]; ring
    have hw' := hw.trans (mul_le_mul_of_nonneg_left (scaled_linear_le_holder hd hd3 hγ) hCw)
    rw [weightedLocalFunction,dite_eq_left q.1.property,weightedLocalFunction,dite_eq_left r.1.property]
    have hid : P.weight p (P.charts.chart p q.1)*localFun ℝ u ⟨p,q⟩-
        P.weight p (P.charts.chart p r.1)*localFun ℝ u ⟨p,r⟩ =
        P.weight p (P.charts.chart p q.1)*(localFun ℝ u ⟨p,q⟩-localFun ℝ u ⟨p,r⟩)+
        (P.weight p (P.charts.chart p q.1)-P.weight p (P.charts.chart p r.1))*localFun ℝ u ⟨p,r⟩ := by ring
    change |P.weight p (P.charts.chart p q.1)*localFun ℝ u ⟨p,q⟩-
      P.weight p (P.charts.chart p r.1)*localFun ℝ u ⟨p,r⟩| ≤ _
    rw [hid]
    calc
      _ ≤ |P.weight p (P.charts.chart p q.1)| * |localFun ℝ u ⟨p,q⟩-localFun ℝ u ⟨p,r⟩|+
          |P.weight p (P.charts.chart p q.1)-P.weight p (P.charts.chart p r.1)| * |localFun ℝ u ⟨p,r⟩| := by
        simpa only [abs_mul] using abs_add_le
          (P.weight p (P.charts.chart p q.1)*(localFun ℝ u ⟨p,q⟩-localFun ℝ u ⟨p,r⟩))
          ((P.weight p (P.charts.chart p q.1)-P.weight p (P.charts.chart p r.1))*localFun ℝ u ⟨p,r⟩)
      _ ≤ 1*(‖u‖*d^γ)+(Cw*((3 : ℝ)^(1-γ)*d^γ))*‖u‖ := by
        apply add_le_add
        · apply mul_le_mul _ hu (abs_nonneg _) zero_le_one
          rw [abs_of_nonneg (P.weight_nonneg p _)]
          exact P.weight_le_one p _
        · exact mul_le_mul hw' hv (abs_nonneg _) (by positivity)
      _ = ((1+Cw*(3 : ℝ)^(1-γ))*‖u‖)*d^γ := by ring

end Yau.LeafProofs.L17LocalScalarAssemblyAux
