import Yau.Proofs.C07RadialCurvePath

open scoped Manifold Topology ContDiff

noncomputable section

namespace Yau.Proofs.C07RadialCurveAux

open Yau Yau.Blueprint Set Filter MeasureTheory

variable {n : ℕ} {M : ComplexManifold n}

theorem radial_speed_integrable {k₀ k₁ : HermitianField M} {o : M.Carrier}
    {Φ : ComplexVector n → M.Carrier} {r c C : ℝ}
    (hk₁ : MetricSmooth k₁) (hΦ : UnitaryChart k₀ o Φ r c C)
    {z : ComplexVector n} (hz : ‖z‖ < r) :
    IntegrableOn (curveSpeed k₁ (radialPiecewise hΦ hz)) (Icc (0 : ℝ) 1) := by
  let S : ℝ → ℝ := fun t => Real.sqrt (2 * hermitianNormSq (k₁ (Φ (t • z)))
    (mfderiv 𝓘(ℂ, ComplexVector n) (ComplexModel n) Φ (t • z) z))
  have hS : ContinuousOn S (Icc (0 : ℝ) 1) :=
    Real.continuous_sqrt.comp_continuousOn (continuousOn_const.mul
      ((pullback_energy_continuousOn k₁ hk₁ hΦ.1.1 z).comp
        (continuous_id.smul continuous_const).continuousOn (fun _ ht => radial_point_mem hz ht)))
  have heq : curveSpeed k₁ (radialPiecewise hΦ hz) =ᵐ[volume.restrict (Icc (0 : ℝ) 1)] S := by
    rw [← Measure.restrict_congr_set (Ioo_ae_eq_Icc (μ := volume))]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact radial_speed_eq hΦ hz ht
  exact (hS.integrableOn_compact isCompact_Icc).congr heq.symm

def radialIntegrable {k₀ k₁ : HermitianField M} {o : M.Carrier}
    {Φ : ComplexVector n → M.Carrier} {r c C : ℝ}
    (hk₁ : MetricSmooth k₁) (hΦ : UnitaryChart k₀ o Φ r c C)
    {z : ComplexVector n} (hz : ‖z‖ < r) : IntegrableCurve k₁ o (Φ z) :=
  ⟨radialPiecewise hΦ hz, radial_speed_integrable hk₁ hΦ hz⟩

theorem radial_speed_le {k₀ k₁ : HermitianField M} {o : M.Carrier}
    {Φ : ComplexVector n → M.Carrier} {r c C : ℝ}
    (horder : ∀ y, HermLE (gMat k₁ y) (gMat k₀ y)) (hC : 0 < C)
    (hΦ : UnitaryChart k₀ o Φ r c C) {z : ComplexVector n} (hz : ‖z‖ < r)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    curveSpeed k₁ (radialPiecewise hΦ hz) t ≤ Real.sqrt (2 * C) * ‖z‖ := by
  rw [radial_speed_eq hΦ hz ht]
  have htz := radial_point_mem hz ⟨ht.1.le, ht.2.le⟩
  have hm := hermitianNormSq_mono horder (Φ (t • z))
    (mfderiv 𝓘(ℂ, ComplexVector n) (ComplexModel n) Φ (t • z) z)
  have hu := (C07Aux.unitaryChart_derivative_bounds hΦ htz z).2
  calc
    _ ≤ Real.sqrt ((2 * C) * ‖z‖ ^ 2) := Real.sqrt_le_sqrt (by linarith)
    _ = Real.sqrt (2 * C) * ‖z‖ := by
      rw [Real.sqrt_mul (by positivity : 0 ≤ 2 * C), Real.sqrt_sq (norm_nonneg z)]

/-- The actual chart radial segment, with a legal extension to all real
parameters, is an integrable curve with the precise factor-two length bound. -/
theorem exists_radial_curve {k₀ k₁ : HermitianField M} {o : M.Carrier}
    {Φ : ComplexVector n → M.Carrier} {r c C : ℝ}
    (hk₁ : MetricSmooth k₁) (horder : ∀ y, HermLE (gMat k₁ y) (gMat k₀ y))
    (hC : 0 < C) (hΦ : UnitaryChart k₀ o Φ r c C)
    {z : ComplexVector n} (hz : ‖z‖ < r) :
    ∃ γ : IntegrableCurve k₁ o (Φ z),
      (∀ t ∈ Icc (0 : ℝ) 1, γ.1 t = Φ ((t : ℂ) • z)) ∧
      curveLength k₁ γ.1 ≤ Real.sqrt (2 * C) * ‖z‖ := by
  refine ⟨radialIntegrable hk₁ hΦ hz, ?_, ?_⟩
  · intro t ht
    exact radialPath_eq Φ z ht
  · have hbound : curveSpeed k₁ (radialPiecewise hΦ hz)
        ≤ᵐ[volume.restrict (Icc (0 : ℝ) 1)] (fun _ => Real.sqrt (2 * C) * ‖z‖) := by
      rw [← Measure.restrict_congr_set (Ioo_ae_eq_Icc (μ := volume))]
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      exact radial_speed_le horder hC hΦ hz ht
    have h := integral_mono_ae (radial_speed_integrable hk₁ hΦ hz)
      (integrableOn_const (isCompact_Icc.measure_lt_top.ne)) hbound
    simpa [radialIntegrable, curveLength, setIntegral_const, Measure.real] using h

end Yau.Proofs.C07RadialCurveAux
