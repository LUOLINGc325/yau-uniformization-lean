import Yau.Proofs.C07ChartChordPath

open scoped Manifold Topology ContDiff

noncomputable section

namespace Yau.Proofs.C07ChartChordAux

open Yau Set Filter MeasureTheory

variable {n : ℕ} {M : ComplexManifold n}

theorem chord_speed_integrable {k : HermitianField M} (hk : MetricSmooth k)
    {ψ : ComplexVector n → M.Carrier} {r R : ℝ}
    (hψ : ContMDiffOn 𝓘(ℂ, ComplexVector n) (ComplexModel n) ∞ ψ (Metric.ball 0 r))
    (hRr : R < r) {a b : ComplexVector n}
    (ha : a ∈ Metric.ball 0 R) (hb : b ∈ Metric.ball 0 R) :
    IntegrableOn (curveSpeed k (chordPiecewise hψ hRr ha hb)) (Icc (0 : ℝ) 1) := by
  let S : ℝ → ℝ := fun t => Real.sqrt (2 * chartEnergy k ψ (a + t • (b - a)) (b - a))
  have hE : ContinuousOn (fun t : ℝ => chartEnergy k ψ (a + t • (b - a)) (b - a))
      (Icc (0 : ℝ) 1) :=
    (C07RadialCurveAux.pullback_energy_continuousOn k hk hψ (b - a)).comp
      (continuous_const.add (continuous_id.smul continuous_const)).continuousOn
      (fun t ht => Metric.ball_subset_ball hRr.le (chord_point_mem ha hb ht))
  have hS : ContinuousOn S (Icc (0 : ℝ) 1) :=
    Real.continuous_sqrt.comp_continuousOn (continuousOn_const.mul hE)
  have heq : curveSpeed k (chordPiecewise hψ hRr ha hb) =ᵐ[volume.restrict (Icc (0 : ℝ) 1)] S := by
    rw [← Measure.restrict_congr_set (Ioo_ae_eq_Icc (μ := volume))]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact chord_speed_eq k hψ hRr ha hb ht
  exact (hS.integrableOn_compact isCompact_Icc).congr heq.symm

def chordIntegrable {k : HermitianField M} (hk : MetricSmooth k)
    {ψ : ComplexVector n → M.Carrier} {r R : ℝ}
    (hψ : ContMDiffOn 𝓘(ℂ, ComplexVector n) (ComplexModel n) ∞ ψ (Metric.ball 0 r))
    (hRr : R < r) {a b : ComplexVector n}
    (ha : a ∈ Metric.ball 0 R) (hb : b ∈ Metric.ball 0 R) :
    IntegrableCurve k (ψ a) (ψ b) :=
  ⟨chordPiecewise hψ hRr ha hb, chord_speed_integrable hk hψ hRr ha hb⟩

theorem chordIntegrable_apply {k : HermitianField M} (hk : MetricSmooth k)
    {ψ : ComplexVector n → M.Carrier} {r R : ℝ}
    (hψ : ContMDiffOn 𝓘(ℂ, ComplexVector n) (ComplexModel n) ∞ ψ (Metric.ball 0 r))
    (hRr : R < r) {a b : ComplexVector n}
    (ha : a ∈ Metric.ball 0 R) (hb : b ∈ Metric.ball 0 R) (t : ℝ) :
    (chordIntegrable hk hψ hRr ha hb).1 t = chordPath ψ a b t := rfl

theorem chord_length_le {k : HermitianField M} (hk : MetricSmooth k)
    {ψ : ComplexVector n → M.Carrier} {r R C : ℝ}
    (hψ : ContMDiffOn 𝓘(ℂ, ComplexVector n) (ComplexModel n) ∞ ψ (Metric.ball 0 r))
    (hRr : R < r) (hC : 0 < C)
    (hbound : ∀ q ∈ Metric.closedBall (0 : ComplexVector n) R,
      ∀ v : ComplexVector n, chartEnergy k ψ q v ≤ C * ‖v‖ ^ 2)
    {a b : ComplexVector n} (ha : a ∈ Metric.ball 0 R) (hb : b ∈ Metric.ball 0 R) :
    curveLength k (chordIntegrable hk hψ hRr ha hb).1 ≤ Real.sqrt (2 * C) * ‖b - a‖ := by
  have hs : curveSpeed k (chordPiecewise hψ hRr ha hb)
      ≤ᵐ[volume.restrict (Icc (0 : ℝ) 1)] (fun _ => Real.sqrt (2 * C) * ‖b - a‖) := by
    rw [← Measure.restrict_congr_set (Ioo_ae_eq_Icc (μ := volume))]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    rw [chord_speed_eq k hψ hRr ha hb ht]
    have hq := hbound (a + t • (b - a))
      (Metric.ball_subset_closedBall (chord_point_mem ha hb ⟨ht.1.le, ht.2.le⟩)) (b - a)
    calc
      _ ≤ Real.sqrt ((2 * C) * ‖b - a‖ ^ 2) := Real.sqrt_le_sqrt (by linarith)
      _ = _ := by
        rw [Real.sqrt_mul (by positivity : 0 ≤ 2 * C), Real.sqrt_sq (norm_nonneg _)]
  have h := integral_mono_ae (chord_speed_integrable hk hψ hRr ha hb)
    (integrableOn_const (isCompact_Icc.measure_lt_top.ne)) hs
  simpa [chordIntegrable, curveLength, setIntegral_const, Measure.real] using h

/-- The uniform bound also applies to the explicitly chosen chord data,
so endpoint-dependent families do not require a choice of arbitrary curves. -/
theorem exists_chord_length_bound {k : HermitianField M} (hk : MetricSmooth k)
    {ψ : ComplexVector n → M.Carrier} {r R : ℝ}
    (hψ : ContMDiffOn 𝓘(ℂ, ComplexVector n) (ComplexModel n) ∞ ψ (Metric.ball 0 r))
    (hRr : R < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ComplexVector n) (ha : a ∈ Metric.ball 0 R)
      (b : ComplexVector n) (hb : b ∈ Metric.ball 0 R),
      curveLength k (chordIntegrable hk hψ hRr ha hb).1 ≤ Real.sqrt (2 * C) * ‖b - a‖ := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_differential_bound k hk hψ hRr
  exact ⟨C, hC, fun _ ha _ hb => chord_length_le hk hψ hRr hC hbound ha hb⟩

/-- A single positive constant works for every pair in the smaller ball.
No injectivity or unitary normalization of the smooth chart map is required. -/
theorem exists_chart_chord {k : HermitianField M} (hk : MetricSmooth k)
    {ψ : ComplexVector n → M.Carrier} {r R : ℝ}
    (hψ : ContMDiffOn 𝓘(ℂ, ComplexVector n) (ComplexModel n) ∞ ψ (Metric.ball 0 r))
    (_hR : 0 < R) (hRr : R < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ a ∈ Metric.ball (0 : ComplexVector n) R,
      ∀ b ∈ Metric.ball (0 : ComplexVector n) R,
      ∃ γ : IntegrableCurve k (ψ a) (ψ b),
        (∀ t ∈ Icc (0 : ℝ) 1, γ.1 t = ψ ((1 - (t : ℂ)) • a + (t : ℂ) • b)) ∧
        curveLength k γ.1 ≤ Real.sqrt (2 * C) * ‖b - a‖ := by
  obtain ⟨C, hC, hbound⟩ := exists_chord_length_bound hk hψ hRr
  refine ⟨C, hC, ?_⟩
  intro a ha b hb
  refine ⟨chordIntegrable hk hψ hRr ha hb, ?_, hbound a ha b hb⟩
  intro t ht
  exact chordPath_eq ψ a b ht

end Yau.Proofs.C07ChartChordAux
