import Yau.Proofs.F02Averages

/-! The original F02 conclusion from exact registered transitive parents.
The G04, P07 and P08 contracts remain explicit conditional dependencies. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
open MeasureTheory Filter

namespace Yau.Proofs
open Yau Blueprint F02Aux
open LeafProofs.L18Aux

/-- The full original metric-defect estimate, with the given flow, its
actual trace integrand, and one constant before all volumes, radii and times.
Every analytic step is proved internally; only exact registered ancestors
P07, P08 and G04 remain as conditional dependencies. -/
theorem F02_of_P07_P08_G04 (hP07 : P07) (hP08 : P08) (hG04 : G04) : F02 := by
  intro n X o h U P ρ hf T hT
  obtain ⟨u, hu⟩ := hP07 n X o
  obtain ⟨A₀, hA₀, hub⟩ := hu.2.2.2
  let A : ℝ := max A₀ 1
  have hA₁ : 1 ≤ A := le_max_right _ _
  have hA : 0 < A := zero_lt_one.trans_le hA₁
  have hA₀A : A₀ ≤ A := le_max_left _ _
  let D : ℝ := 3 * A₀ * A + 1
  have hD₁ : 1 ≤ D := by
    dsimp [D]
    have hpos := mul_pos (mul_pos (by norm_num : (0 : ℝ) < 3) hA₀) hA
    linarith
  have hD : 0 < D := zero_lt_one.trans_le hD₁
  obtain ⟨K, hK, hcutoffLap⟩ := exhaustionCutoff_laplacian_bound X o u hu
  obtain ⟨B₀, hB₀⟩ := (hP08 n X o).2
  let B : ℝ := max B₀ 1
  have hB : 0 < B := zero_lt_one.trans_le (le_max_right _ _)
  obtain ⟨J, hJ, hPotential⟩ := neg_potential_ball_average X o h U P ρ hf T hT
  let E : ℝ := B / D + K * J * D
  have hE : 0 < E := by dsimp [E]; positivity
  let C : ℝ := E * D ^ (2 * n) + 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, fun μ hμ L hL t ht => ?_⟩
  have ht0 : 0 ≤ t := ht.1
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  have hDL : 0 < D * L := mul_pos hD hLpos
  have hDL₁ : 1 ≤ D * L := by
    simpa only [one_mul] using mul_le_mul hD₁ hL zero_le_one hD.le
  have hLR : L ≤ D * L := by nlinarith
  refine ⟨fun x => metricDefect_trace_bounds X o h U P ρ hf ht.1 x, ?_⟩
  let a := fun x => traceWith (gMat X.metric.form x) (gMat X.metric.form x - gMat (h t) x)
  let v := fun x => -U x t
  have ha := metricDefect_smooth_of_G04 hG04 X o h U P ρ hf ht.1
  have ha0 : ∀ x, 0 ≤ a x := fun x => (metricDefect_trace_bounds X o h U P ρ hf ht.1 x).1
  have hv : SmoothFn v := fun x =>
    (LeafProofs.L19Aux.smoothSpaceTime_slice hf.2.1 ht.1 x).neg
  have hv0 : ∀ x, 0 ≤ v x := fun x => neg_nonneg.mpr (potential_nonpos X o h U P ρ hf ht.1 x)
  have hRs := scalarCurvature_smooth_of_G04 hG04 X
  have hR0 := initial_scalarCurvature_nonneg X o h U P ρ hf
  have hCurvAvg : BallIntegralLE X.metric.form μ o (scalarCurvature X.metric.form)
      (D * L) (B / (D * L)) :=
    ballIntegralLE_mono_bound _ _ _ _ _ (hB₀ μ hμ (D * L) hDL₁)
      (div_le_div_of_nonneg_right (le_max_left _ _) hDL.le)
  have hCurv := (ballIntegralLE_iff_real X.metric μ hμ o _ hDL
    (div_nonneg hB.le hDL.le) (smoothFn_integrableOn_distBall X.metric μ hμ hRs o hDL) hR0).mp hCurvAvg
  have hPot := (ballIntegralLE_iff_real X.metric μ hμ o _ hDL
    (by positivity : 0 ≤ J * t * (D * L))
    (smoothFn_integrableOn_distBall X.metric μ hμ hv o hDL) hv0).mp
      (hPotential μ hμ (D * L) hDL₁ t ht)
  have hWeighted := metricDefect_integral_cutoff_bound hG04 X o h U P ρ hf μ hμ
    ht.1 hLpos hDL (by positivity : 0 ≤ K / L ^ 2)
    (exhaustionCutoff u A L) (exhaustionCutoff_smooth hu.1 A L)
    (exhaustionCutoff_compact X o u hu hA hLpos)
    (exhaustionCutoff_range u A L)
    (exhaustionCutoff_one_on_ball X o u hu A₀ hA₀ (fun x => (hub x).2.1) hA₀A hA hL)
    (exhaustionCutoff_tsupport_ball X o u hu A₀ hA₀ (fun x => (hub x).1) hA hLpos)
    (hcutoffLap A hA₁ L hL)
  have hBG := flow_initial_volume_comparison X o h U P ρ hf μ hμ hLpos hLR
  rw [mul_div_cancel_right₀ D hLpos.ne'] at hBG
  have hVolume : (μ (distBall X.metric.form o (D * L))).toReal ≤
      D ^ (2 * n) * (μ (distBall X.metric.form o L)).toReal := by
    have h := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (distBall_measure_lt_top X.metric μ hμ o hLpos).ne) hBG
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hD.le _)] using h
  apply (ballIntegralLE_iff_real X.metric μ hμ o a hLpos
    (div_nonneg (mul_nonneg hC.le ht.1) hLpos.le)
    (smoothFn_integrableOn_distBall X.metric μ hμ ha o hLpos) ha0).mpr
  calc
    (∫ x in distBall X.metric.form o L, a x ∂μ) ≤
        t * (∫ x in distBall X.metric.form o (D * L), scalarCurvature X.metric.form x ∂μ) +
          (K / L ^ 2) * (∫ x in distBall X.metric.form o (D * L), v x ∂μ) := hWeighted
    _ ≤ t * (B / (D * L) * (μ (distBall X.metric.form o (D * L))).toReal) +
        (K / L ^ 2) * (J * t * (D * L) * (μ (distBall X.metric.form o (D * L))).toReal) :=
      add_le_add (mul_le_mul_of_nonneg_left hCurv ht.1)
        (mul_le_mul_of_nonneg_left hPot (by positivity))
    _ = E * t / L * (μ (distBall X.metric.form o (D * L))).toReal := by
      dsimp [E]
      field_simp
    _ ≤ E * t / L * (D ^ (2 * n) * (μ (distBall X.metric.form o L)).toReal) :=
      mul_le_mul_of_nonneg_left hVolume (by positivity)
    _ = (E * D ^ (2 * n)) * t / L * (μ (distBall X.metric.form o L)).toReal := by ring
    _ ≤ C * t / L * (μ (distBall X.metric.form o L)).toReal := by
      apply mul_le_mul_of_nonneg_right _ ENNReal.toReal_nonneg
      apply div_le_div_of_nonneg_right _ hLpos.le
      exact mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) ht.1

end Yau.Proofs
