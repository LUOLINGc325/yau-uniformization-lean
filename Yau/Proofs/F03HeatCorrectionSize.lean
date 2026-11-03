import Yau.Proofs.F03HodgeHeatCorrection
import Yau.Proofs.F03MetricDefectHeatMajorants

/-! The actual heat correction vanishes initially, is nonpositive, and has the fractional size bound. -/
noncomputable section
open MeasureTheory Set
open scoped ComplexOrder Interval
namespace Yau.Proofs.F03Aux
open Yau Blueprint HeatConcreteBindings HeatTargetCandidates
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem metricDefectHeatCorrection_zero
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    (O : ℕ → Set (Pt X)) (hO : SmoothExhaustion O) (L : ℝ) (x : Pt X) :
    metricDefectHeatCorrection X h μ hμ O hO L x 0=0 := by
  have hz : flowMetricDefect X h 0=0 := funext (F02Aux.metricDefect_zero X o h U P ρ hf)
  simp [metricDefectHeatCorrection,hz,boundedKernelEvolution]

theorem metricDefectHeatCorrection_nonpos
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    (O : ℕ → Set (Pt X)) (hO : SmoothExhaustion O) (L : ℝ) (x : Pt X)
    {s : ℝ} (hs : 0 ≤ s) : metricDefectHeatCorrection X h μ hμ O hO L x s ≤ 0 := by
  apply neg_nonpos.mpr
  apply intervalIntegral.integral_nonneg (sq_nonneg L)
  intro b hb
  exact dirichletMinimalBoundedHeat_nonnegative X.metric X.kahler_metric μ hμ O hO
    (flowMetricDefect X h s) (fun y => (flowMetricDefect_bounds X o h U P ρ hf hs y).1) hb.1 x

theorem metricDefectHeatCorrection_size_bound (hP06 : P06) (hP07 : P07) (hP08 : P08)
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) {T : ℝ} (hT : 0 < T)
    (C₀ : ℝ) (hC₀ : 0 ≤ C₀) :
    ∃ C : ℝ,0 < C ∧
      ∀ (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
        (O : ℕ → Set (Pt X)) (hO : SmoothExhaustion O)
        (s : ℝ),s ∈ Icc 0 T → ∀ L : ℝ,1 ≤ L →
      ∀ x,inducedDistance X.metric.form o x ≤ C₀*L →
      |metricDefectHeatCorrection X h μ hμ O hO L x s| ≤
        C*s^(heatDecayExponent n)*L^(2-heatDecayExponent n) := by
  obtain ⟨K,hK,hEstimate⟩ := flowMetricDefect_heat_quarter_majorants hP07 hP08 X o h U P ρ hf hT C₀ hC₀
  refine ⟨K*(4/3),by positivity,fun μ hμ O hO s hs L hL x hx => ?_⟩
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  rcases eq_or_lt_of_le hs.1 with hs0|hs0
  · subst s
    rw [metricDefectHeatCorrection_zero X o h U P ρ hf,abs_zero]
    positivity
  obtain ⟨V,_hV,_hPositive,hPotential⟩ := flowMetricDefect_hodge_heat_correction hP06 X o h U P ρ hf hs.1
  have hInt := ((hPotential μ hμ O hO).2 L hL0).1 x
  have hMajorInt : IntervalIntegrable
      (fun b : ℝ => K*(s^(heatDecayExponent n)*L^((1:ℝ)/2-heatDecayExponent n)*b^(-(1:ℝ)/4)))
      volume 0 (L^2) := ((quarter_heat_majorant_integrable (L^2)).1.const_mul _).const_mul K
  have hNonneg : 0 ≤ ∫ b in (0:ℝ)..L^2,boundedKernelEvolution μ
      (dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO) (flowMetricDefect X h s) b x :=
    neg_nonpos.mp (metricDefectHeatCorrection_nonpos X o h U P ρ hf μ hμ O hO L x hs.1)
  rw [metricDefectHeatCorrection,abs_neg,abs_of_nonneg hNonneg]
  calc
    _ ≤ ∫ b in (0:ℝ)..L^2,K*(s^(heatDecayExponent n)*L^((1:ℝ)/2-heatDecayExponent n)*b^(-(1:ℝ)/4)) := by
      apply intervalIntegral.integral_mono_on_of_le_Ioo (sq_nonneg L) hInt hMajorInt
      intro b hb
      convert (hEstimate μ hμ O hO s ⟨hs0,hs.2⟩ L hL b hb.1 hb.2.le x hx).1 using 1 <;> ring
    _ = _ := by
      rw [intervalIntegral.integral_const_mul,heat_quarter_majorant_scale_integral hL0]
      ring

end Yau.Proofs.F03Aux
