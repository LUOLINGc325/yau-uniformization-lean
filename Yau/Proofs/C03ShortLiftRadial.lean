import Yau.Proofs.C07RadialCurvePath

/-! Actual radial curves need only complex smoothness, with no unitary normalization. -/
noncomputable section
open scoped Manifold Topology ContDiff
namespace Yau.Proofs.C03Aux.ShortLift
open Yau Yau.Blueprint Set Filter MeasureTheory C07RadialCurveAux
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {M : ComplexManifold n}

def radialCurve {o : M.Carrier}
    {Φ : ComplexVector n → M.Carrier} {r : ℝ}
    (hF0 : Φ 0 = o)
    (hF : ContMDiffOn (ComplexModel n) (ComplexModel n) ∞ Φ (Metric.ball 0 r))
    {z : ComplexVector n} (hz : ‖z‖ < r) : PiecewiseC1Curve o (Φ z) where
  toFun := radialPath Φ z
  start_eq := by simpa [radialPath, radialClamp] using hF0
  finish_eq := by simp [radialPath, radialClamp]
  breakpoints := {0, 1}
  breakpoints_mem := by intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht; rcases ht with rfl | rfl <;> norm_num
  continuous_on := (radialPath_continuous hF hz).continuousOn
  piecewise_c1 := by
    intro t ht
    have hts : t ≠ 0 ∧ t ≠ 1 := by simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using ht
    exact radialPath_piecewise_c1 hF hz hts.1 hts.2

theorem radial_derivative {o : M.Carrier}
    {Φ : ComplexVector n → M.Carrier} {r : ℝ}
    (hF0 : Φ 0 = o)
    (hF : ContMDiffOn (ComplexModel n) (ComplexModel n) ∞ Φ (Metric.ball 0 r)) {z : ComplexVector n} (hz : ‖z‖ < r)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    realTangentDerivative (radialCurve hF0 hF hz) t =
      mfderiv 𝓘(ℂ, ComplexVector n) (ComplexModel n) Φ (t • z) z := by
  let G : ComplexVector n → ComplexVector n := fun w => chartPt (Φ (t • z)) (Φ w)
  have htz := radial_point_mem hz ⟨ht.1.le, ht.2.le⟩
  have hΦt := hF.contMDiffAt (Metric.isOpen_ball.mem_nhds htz)
  have hG : ContDiffAt ℂ ∞ G (t • z) :=
    (contMDiffAt_extChartAt.comp (t • z) hΦt).contDiffAt
  have hGD := (hG.differentiableAt (by simp)).hasFDerivAt.restrictScalars ℝ
  have hline : HasDerivAt (fun s : ℝ => s • z) z t := by
    simpa using (hasDerivAt_id t).smul_const z
  have hcomp := hGD.comp_hasDerivAt t hline
  have heq : (fun s : ℝ => chartPt ((radialCurve hF0 hF hz) t)
      ((radialCurve hF0 hF hz) s)) =ᶠ[𝓝 t] (fun s => G (s • z)) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    change chartPt (radialPath Φ z t) (radialPath Φ z s) = G (s • z)
    rw [radialPath_eq Φ z ⟨ht.1.le, ht.2.le⟩, radialPath_eq Φ z ⟨hs.1.le, hs.2.le⟩]
    rfl
  have hder := hcomp.congr_of_eventuallyEq heq
  have hself := mfderivWithin_range_extChartAt_symm (I := ComplexModel n)
    (x := (radialCurve hF0 hF hz) t)
  simp only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] at hself
  unfold realTangentDerivative
  rw [hself]
  change deriv (fun s : ℝ => chartPt ((radialCurve hF0 hF hz) t)
    ((radialCurve hF0 hF hz) s)) t = _
  rw [hder.deriv]
  unfold mfderiv
  rw [if_pos (hΦt.mdifferentiableAt (by simp))]
  simp only [ModelWithCorners.range_eq_univ, fderivWithin_univ]
  rfl

theorem radial_speed_eq {k₁ : HermitianField M} {o : M.Carrier}
    {Φ : ComplexVector n → M.Carrier} {r : ℝ}
    (hF0 : Φ 0 = o)
    (hF : ContMDiffOn (ComplexModel n) (ComplexModel n) ∞ Φ (Metric.ball 0 r)) {z : ComplexVector n} (hz : ‖z‖ < r)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    curveSpeed k₁ (radialCurve hF0 hF hz) t =
      Real.sqrt (2 * hermitianNormSq (k₁ (Φ (t • z)))
        (mfderiv 𝓘(ℂ, ComplexVector n) (ComplexModel n) Φ (t • z) z)) := by
  unfold curveSpeed
  rw [radial_derivative hF0 hF hz ht]
  change Real.sqrt (2 * hermitianNormSq (k₁ (radialPath Φ z t)) _) = _
  rw [radialPath_eq Φ z ⟨ht.1.le, ht.2.le⟩]
  rfl

theorem radial_speed_integrable {k₁ : HermitianField M} {o : M.Carrier}
    {Φ : ComplexVector n → M.Carrier} {r : ℝ}
    (hk₁ : MetricSmooth k₁) (hF0 : Φ 0 = o)
    (hF : ContMDiffOn (ComplexModel n) (ComplexModel n) ∞ Φ (Metric.ball 0 r))
    {z : ComplexVector n} (hz : ‖z‖ < r) :
    IntegrableOn (curveSpeed k₁ (radialCurve hF0 hF hz)) (Icc (0 : ℝ) 1) := by
  let S : ℝ → ℝ := fun t => Real.sqrt (2 * hermitianNormSq (k₁ (Φ (t • z)))
    (mfderiv 𝓘(ℂ, ComplexVector n) (ComplexModel n) Φ (t • z) z))
  have hS : ContinuousOn S (Icc (0 : ℝ) 1) :=
    Real.continuous_sqrt.comp_continuousOn (continuousOn_const.mul
      ((pullback_energy_continuousOn k₁ hk₁ hF z).comp
        (continuous_id.smul continuous_const).continuousOn (fun _ ht => radial_point_mem hz ht)))
  have heq : curveSpeed k₁ (radialCurve hF0 hF hz) =ᵐ[volume.restrict (Icc (0 : ℝ) 1)] S := by
    rw [← Measure.restrict_congr_set (Ioo_ae_eq_Icc (μ := volume))]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact radial_speed_eq hF0 hF hz ht
  exact (hS.integrableOn_compact isCompact_Icc).congr heq.symm

def radialIntegrable {k : HermitianField M} {o : M.Carrier}
    {Φ : ComplexVector n → M.Carrier} {r : ℝ}
    (hk : MetricSmooth k) (hF0 : Φ 0 = o)
    (hF : ContMDiffOn (ComplexModel n) (ComplexModel n) ∞ Φ (Metric.ball 0 r))
    {z : ComplexVector n} (hz : ‖z‖ < r) : IntegrableCurve k o (Φ z) :=
  ⟨radialCurve hF0 hF hz, radial_speed_integrable hk hF0 hF hz⟩

theorem exists_radial_curve {k : HermitianField M} {o : M.Carrier}
    {Φ : ComplexVector n → M.Carrier} {r L : ℝ}
    (hk : MetricSmooth k) (hF0 : Φ 0 = o)
    (hF : ContMDiffOn (ComplexModel n) (ComplexModel n) ∞ Φ (Metric.ball 0 r))
    (hL : 0 < L)
    (hbound : ∀ q ∈ Metric.ball 0 r, ∀ v : ComplexVector n,
      2 * hermitianNormSq (k (Φ q))
        (mfderiv (ComplexModel n) (ComplexModel n) Φ q v) ≤ L ^ 2 * ‖v‖ ^ 2)
    {z : ComplexVector n} (hz : ‖z‖ < r) :
    ∃ γ : IntegrableCurve k o (Φ z),
      (∀ t ∈ Icc (0 : ℝ) 1, γ.1 t = Φ (t • z)) ∧ curveLength k γ.1 ≤ L * ‖z‖ := by
  refine ⟨radialIntegrable hk hF0 hF hz, ?_, ?_⟩
  · intro t ht
    exact radialPath_eq Φ z ht
  · have hbound' : curveSpeed k (radialCurve hF0 hF hz)
        ≤ᵐ[volume.restrict (Icc (0 : ℝ) 1)] (fun _ => L * ‖z‖) := by
      rw [← Measure.restrict_congr_set (Ioo_ae_eq_Icc (μ := volume))]
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      rw [radial_speed_eq hF0 hF hz ht]
      calc
        _ ≤ Real.sqrt (L ^ 2 * ‖z‖ ^ 2) :=
          Real.sqrt_le_sqrt (hbound _ (radial_point_mem hz ⟨ht.1.le, ht.2.le⟩) z)
        _ = L * ‖z‖ := by
          rw [Real.sqrt_mul (sq_nonneg L), Real.sqrt_sq hL.le, Real.sqrt_sq (norm_nonneg z)]
    have H := integral_mono_ae (radial_speed_integrable hk hF0 hF hz)
      (integrableOn_const (isCompact_Icc.measure_lt_top.ne)) hbound'
    simpa [radialIntegrable, curveLength, setIntegral_const, Measure.real] using H

end Yau.Proofs.C03Aux.ShortLift
