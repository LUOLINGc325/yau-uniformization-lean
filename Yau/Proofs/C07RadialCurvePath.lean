import Yau.Proofs.C07RadialCurveMetric

open scoped Manifold Topology ContDiff

noncomputable section

namespace Yau.Proofs.C07RadialCurveAux

open Yau Yau.Blueprint Set Filter MeasureTheory

def radialClamp (t : ℝ) : ℝ := max 0 (min 1 t)

theorem radialClamp_mem (t : ℝ) : radialClamp t ∈ Icc (0 : ℝ) 1 := by
  exact ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

theorem radialClamp_eq {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : radialClamp t = t := by
  simp only [radialClamp, min_eq_right ht.2, max_eq_right ht.1]

theorem radialClamp_of_neg {t : ℝ} (ht : t < 0) : radialClamp t = 0 := by
  simp only [radialClamp, min_eq_right (by linarith : t ≤ 1), max_eq_left ht.le]

theorem radialClamp_of_gt_one {t : ℝ} (ht : 1 < t) : radialClamp t = 1 := by
  simp only [radialClamp, min_eq_left ht.le, max_eq_right zero_le_one]

theorem continuous_radialClamp : Continuous radialClamp :=
  continuous_const.max (continuous_const.min continuous_id)

variable {n : ℕ} {M : ComplexManifold n}

theorem radial_point_mem {r : ℝ} {z : ComplexVector n} (hz : ‖z‖ < r)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : t • z ∈ Metric.ball 0 r := by
  rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_of_nonneg ht.1]
  exact (mul_le_of_le_one_left (norm_nonneg z) ht.2).trans_lt hz

def radialPath (Φ : ComplexVector n → M.Carrier) (z : ComplexVector n) (t : ℝ) : M.Carrier :=
  Φ (radialClamp t • z)

theorem radialPath_eq (Φ : ComplexVector n → M.Carrier) (z : ComplexVector n)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : radialPath Φ z t = Φ ((t : ℂ) • z) := by
  simp only [radialPath, radialClamp_eq ht]
  rfl

theorem radialPath_continuous {Φ : ComplexVector n → M.Carrier} {r : ℝ}
    (hΦ : ContMDiffOn 𝓘(ℂ, ComplexVector n) (ComplexModel n) ∞ Φ (Metric.ball 0 r))
    {z : ComplexVector n} (hz : ‖z‖ < r) : Continuous (radialPath Φ z) :=
  hΦ.continuousOn.comp_continuous (continuous_radialClamp.smul continuous_const)
    (fun t => radial_point_mem hz (radialClamp_mem t))

theorem radialPath_piecewise_c1 {Φ : ComplexVector n → M.Carrier} {r : ℝ}
    (hΦ : ContMDiffOn 𝓘(ℂ, ComplexVector n) (ComplexModel n) ∞ Φ (Metric.ball 0 r))
    {z : ComplexVector n} (hz : ‖z‖ < r) {t : ℝ} (ht₀ : t ≠ 0) (ht₁ : t ≠ 1) :
    ContDiffAt ℝ 1 (fun s : ℝ => chartPt (radialPath Φ z t) (radialPath Φ z s)) t := by
  by_cases ht : t < 0
  · apply (contDiffAt_const (c := chartPt (radialPath Φ z t) (Φ 0))).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds ht] with s hs
    simp only [radialPath, radialClamp_of_neg hs, zero_smul]
  · by_cases ht' : 1 < t
    · apply (contDiffAt_const (c := chartPt (radialPath Φ z t) (Φ z))).congr_of_eventuallyEq
      filter_upwards [Ioi_mem_nhds ht'] with s hs
      simp only [radialPath, radialClamp_of_gt_one hs, one_smul]
    · have hti : t ∈ Ioo (0 : ℝ) 1 :=
        ⟨lt_of_le_of_ne (le_of_not_gt ht) ht₀.symm, lt_of_le_of_ne (le_of_not_gt ht') ht₁⟩
      have htz := radial_point_mem hz ⟨hti.1.le, hti.2.le⟩
      have hΦt := hΦ.contMDiffAt (Metric.isOpen_ball.mem_nhds htz)
      have hG : ContDiffAt ℂ ∞ (fun w => chartPt (Φ (t • z)) (Φ w)) (t • z) :=
        (contMDiffAt_extChartAt.comp (t • z) hΦt).contDiffAt
      have hline : ContDiffAt ℝ 1 (fun s : ℝ => s • z) t :=
        (contDiff_id.smul contDiff_const).contDiffAt
      have hcomp := ((hG.restrict_scalars ℝ).of_le (by simp : (1 : ℕ∞ω) ≤ ∞)).comp t hline
      rw [radialPath_eq Φ z ⟨hti.1.le, hti.2.le⟩]
      apply hcomp.congr_of_eventuallyEq
      filter_upwards [Ioo_mem_nhds hti.1 hti.2] with s hs
      rw [radialPath_eq Φ z ⟨hs.1.le, hs.2.le⟩]
      rfl

def radialPiecewise {k : HermitianField M} {o : M.Carrier}
    {Φ : ComplexVector n → M.Carrier} {r c C : ℝ}
    (hΦ : UnitaryChart k o Φ r c C) {z : ComplexVector n} (hz : ‖z‖ < r) :
    PiecewiseC1Curve o (Φ z) where
  toFun := radialPath Φ z
  start_eq := by simpa [radialPath, radialClamp] using hΦ.2.1
  finish_eq := by simp [radialPath, radialClamp]
  breakpoints := {0, 1}
  breakpoints_mem := by intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht; rcases ht with rfl | rfl <;> norm_num
  continuous_on := (radialPath_continuous hΦ.1.1 hz).continuousOn
  piecewise_c1 := by
    intro t ht
    have hts : t ≠ 0 ∧ t ≠ 1 := by simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using ht
    exact radialPath_piecewise_c1 hΦ.1.1 hz hts.1 hts.2

/-- On the open parameter interval the derivative of the clipped curve
is exactly the differential of the original chart applied to `z`. -/
theorem radial_derivative {k : HermitianField M} {o : M.Carrier}
    {Φ : ComplexVector n → M.Carrier} {r c C : ℝ}
    (hΦ : UnitaryChart k o Φ r c C) {z : ComplexVector n} (hz : ‖z‖ < r)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    realTangentDerivative (radialPiecewise hΦ hz) t =
      mfderiv 𝓘(ℂ, ComplexVector n) (ComplexModel n) Φ (t • z) z := by
  let G : ComplexVector n → ComplexVector n := fun w => chartPt (Φ (t • z)) (Φ w)
  have htz := radial_point_mem hz ⟨ht.1.le, ht.2.le⟩
  have hΦt := hΦ.1.1.contMDiffAt (Metric.isOpen_ball.mem_nhds htz)
  have hG : ContDiffAt ℂ ∞ G (t • z) :=
    (contMDiffAt_extChartAt.comp (t • z) hΦt).contDiffAt
  have hGD := (hG.differentiableAt (by simp)).hasFDerivAt.restrictScalars ℝ
  have hline : HasDerivAt (fun s : ℝ => s • z) z t := by
    simpa using (hasDerivAt_id t).smul_const z
  have hcomp := hGD.comp_hasDerivAt t hline
  have heq : (fun s : ℝ => chartPt ((radialPiecewise hΦ hz) t)
      ((radialPiecewise hΦ hz) s)) =ᶠ[𝓝 t] (fun s => G (s • z)) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    change chartPt (radialPath Φ z t) (radialPath Φ z s) = G (s • z)
    rw [radialPath_eq Φ z ⟨ht.1.le, ht.2.le⟩, radialPath_eq Φ z ⟨hs.1.le, hs.2.le⟩]
    rfl
  have hder := hcomp.congr_of_eventuallyEq heq
  have hself := mfderivWithin_range_extChartAt_symm (I := ComplexModel n)
    (x := (radialPiecewise hΦ hz) t)
  simp only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] at hself
  unfold realTangentDerivative
  rw [hself]
  change deriv (fun s : ℝ => chartPt ((radialPiecewise hΦ hz) t)
    ((radialPiecewise hΦ hz) s)) t = _
  rw [hder.deriv]
  unfold mfderiv
  rw [if_pos (hΦt.mdifferentiableAt (by simp))]
  simp only [ModelWithCorners.range_eq_univ, fderivWithin_univ]
  rfl

theorem radial_speed_eq {k₀ k₁ : HermitianField M} {o : M.Carrier}
    {Φ : ComplexVector n → M.Carrier} {r c C : ℝ}
    (hΦ : UnitaryChart k₀ o Φ r c C) {z : ComplexVector n} (hz : ‖z‖ < r)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    curveSpeed k₁ (radialPiecewise hΦ hz) t =
      Real.sqrt (2 * hermitianNormSq (k₁ (Φ (t • z)))
        (mfderiv 𝓘(ℂ, ComplexVector n) (ComplexModel n) Φ (t • z) z)) := by
  unfold curveSpeed
  rw [radial_derivative hΦ hz ht]
  change Real.sqrt (2 * hermitianNormSq (k₁ (radialPath Φ z t)) _) = _
  rw [radialPath_eq Φ z ⟨ht.1.le, ht.2.le⟩]
  rfl

end Yau.Proofs.C07RadialCurveAux
