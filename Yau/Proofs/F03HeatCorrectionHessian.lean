import Yau.Proofs.F03HodgeHeatCorrection
import Yau.Proofs.F03MetricDefectHeat
import Yau.Proofs.F03TraceOrder

/-! The exact heat correction has the genuine metric-defect Hessian with a uniform small mean error. -/
noncomputable section
open MeasureTheory Set
open scoped ComplexOrder
namespace Yau.Proofs.F03Aux
open Yau Blueprint HeatConcreteBindings HeatTargetCandidates
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem metricDefectHeatCorrection_hessian_bound (hP06 : P06) (hP07 : P07) (hP08 : P08)
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) {T : ℝ} (hT : 0 < T)
    (C₀ : ℝ) (hC₀ : 0 ≤ C₀) :
    ∃ C : ℝ,0 < C ∧
      ∀ (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
        (O : ℕ → Set (Pt X)) (hO : SmoothExhaustion O)
        (s : ℝ),s ∈ Icc 0 T → ∀ L : ℝ,1 ≤ L →
      ∀ x,inducedDistance X.metric.form o x ≤ C₀*L →
      HermLE (gMat X.metric.form x-gMat (h s) x-((C*s/L:ℝ):ℂ) • gMat X.metric.form x)
        (levi (fun y => metricDefectHeatCorrection X h μ hμ O hO L y s) x) ∧
      HermLE (levi (fun y => metricDefectHeatCorrection X h μ hμ O hO L y s) x)
        (gMat X.metric.form x-gMat (h s) x) := by
  obtain ⟨C,hC,hMean⟩ := flowMetricDefect_heat_mean_bound hP07 hP08 X o h U P ρ hf hT C₀ hC₀
  refine ⟨C,hC,fun μ hμ O hO s hs L hL x hx => ?_⟩
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  obtain ⟨V,_hV,hPositive,hData⟩ := flowMetricDefect_hodge_heat_correction hP06 X o h U P ρ hf hs.1
  rcases hData μ hμ O hO with ⟨hTrace,hPotential⟩
  have hIdentity := (hPotential L hL0).2 x
  have hPS := hPositive (L^2) (sq_pos_of_pos hL0) x
  have hTraceBound : traceWith (gMat X.metric.form x) (formHermitianMatrix (V (L^2)) x) ≤ C*s/L := by
    change formTrace X.metric.form (V (L^2)) x ≤ C*s/L
    rw [hTrace (L^2) (sq_pos_of_pos hL0) x]
    have hh := (hMean μ hμ O hO s hs L hL (L^2) (sq_pos_of_pos hL0) le_rfl x hx).trans (min_le_right _ _)
    simpa only [Real.sqrt_sq_eq_abs,abs_of_pos hL0,div_self hL0.ne',one_pow,mul_one] using hh
  have hg := LeafProofs.L18Aux.hMat_posDef X.metric.form x (chartPt x x) (mem_extChartAt_target x)
  have hOrder := posSemidef_le_relative_trace_bound (gMat X.metric.form x)
    (formHermitianMatrix (V (L^2)) x) hg hPS
    (div_nonneg (mul_nonneg hC.le hs.1) hL0.le) hTraceBound
  constructor
  · unfold HermLE at hOrder ⊢
    rw [hIdentity]
    convert hOrder using 1 <;> abel
  · unfold HermLE
    rw [hIdentity]
    convert hPS using 1 <;> abel

end Yau.Proofs.F03Aux
