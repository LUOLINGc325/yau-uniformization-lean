import Yau.Proofs.F03EllipticTranslation

/-! Actual shifted chart powers of the compact heat error are smooth and uniformly O(t). -/
noncomputable section
open Filter Set
open scoped Topology ContDiff
namespace Yau.Proofs.F03Aux
open Yau LeafCandidates LeafProofs.L19Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000

theorem shifted_elliptic_chart_laplacian_power
    (g : SmoothMetric M) {u : M.Carrier → ℝ} (hu : SmoothFn u)
    (a : M.Carrier) (c : ComplexVector n) (m : ℕ) :
    EqOn ((ellipticOp (fun w => scalarHeatChartCoeff g a (w+c,0)) (fun _ _ => 0))^[m]
      (fun w => (inChart (α := ℝ) a u (w+c) : ℂ)))
      (fun w => (inChart (α := ℝ) a ((laplacian g.form)^[m] u) (w+c) : ℂ))
      {w | w+c ∈ chartTarget a} := by
  intro w hw
  have hShift := congrFun (ellipticOp_power_translate
    (fun w => scalarHeatChartCoeff g a (w,0)) (fun _ _ => 0)
    (fun w => (inChart (α := ℝ) a u w : ℂ)) c m) w
  exact hShift.trans (ellipticOp_chart_laplacian_power g hu a m hw)

theorem shifted_elliptic_chart_power_smooth
    (g : SmoothMetric M) {u : M.Carrier → ℝ} (hu : SmoothFn u)
    (a : M.Carrier) (c : ComplexVector n) (m : ℕ) :
    ContDiffOn ℝ ∞
      ((ellipticOp (fun w => scalarHeatChartCoeff g a (w+c,0)) (fun _ _ => 0))^[m]
        (fun w => (inChart (α := ℝ) a u (w+c) : ℂ)))
      {w | w+c ∈ chartTarget a} := by
  have hChart := Complex.ofRealCLM.contDiff.comp_contDiffOn ((smoothFn_laplacian_power g hu m) a)
  have hShift := hChart.comp (contDiff_id.add contDiff_const).contDiffOn
    (show MapsTo (fun w : ComplexVector n => w+c) {w | w+c ∈ chartTarget a} (chartTarget a) from
      fun _ hw => hw)
  exact hShift.congr (shifted_elliptic_chart_laplacian_power g hu a c m)

theorem wholeCompactHeat_shifted_chart_power_rate
    (g : SmoothMetric M) (hK : IsKahler g)
    (μ : MeasureTheory.Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (k : ScalarEnergyDomain g μ hμ) (a : M.Carrier) (c : ComplexVector n) (m : ℕ) :
    ∃ K : ℝ,0 < K ∧ ∀ t,0 < t →
      ContDiffOn ℝ ∞
        ((ellipticOp (fun w => scalarHeatChartCoeff g a (w+c,0)) (fun _ _ => 0))^[m]
          (fun w => ((wholeCompactHeat g hK μ hμ k (chartInv a (w+c)) t-k (chartInv a (w+c)) : ℝ) : ℂ)))
        {w | w+c ∈ chartTarget a} ∧
      ∀ w,w+c ∈ chartTarget a →
        ‖((ellipticOp (fun w => scalarHeatChartCoeff g a (w+c,0)) (fun _ _ => 0))^[m]
          (fun z => ((wholeCompactHeat g hK μ hμ k (chartInv a (z+c)) t-k (chartInv a (z+c)) : ℝ) : ℂ))) w‖ ≤ K*t := by
  obtain ⟨K,hK0,hRate⟩ := wholeCompactHeat_error_power_rate g hK μ hμ k m
  refine ⟨K,hK0,fun t ht => ?_⟩
  have hSmooth := (hRate t ht).1
  refine ⟨shifted_elliptic_chart_power_smooth g hSmooth a c m,fun w hw => ?_⟩
  have hEq := shifted_elliptic_chart_laplacian_power g hSmooth a c m hw
  have hBound : ‖(((laplacian g.form)^[m]
      (fun y => wholeCompactHeat g hK μ hμ k y t-k y)) (chartInv a (w+c)) : ℂ)‖ ≤ K*t := by
    simpa only [Complex.norm_real,Real.norm_eq_abs,mul_comm] using (hRate t ht).2 (chartInv a (w+c))
  exact (congrArg norm hEq).trans_le hBound

end Yau.Proofs.F03Aux
