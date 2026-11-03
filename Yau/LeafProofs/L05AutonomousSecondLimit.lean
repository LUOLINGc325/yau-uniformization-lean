import Yau.LeafProofs.L05AutonomousMollifierAverage
import Yau.LeafProofs.L05AutonomousSecondFTC

noncomputable section
open Filter Set MeasureTheory Matrix
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius BoundedContinuousFunction
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic Yau.LeafProofs.L05Aux

theorem autoSecond_continuous {n : ℕ} {u : Point n → ℝ} (hu : Continuous u) (e : Space n) (h : ℝ) :
    Continuous (autoSecond u e h) := by
  unfold autoSecond
  exact (((hu.comp ((continuous_fst.add continuous_const).prodMk continuous_snd)).add
    (hu.comp ((continuous_fst.sub continuous_const).prodMk continuous_snd))).sub
      (continuous_const.mul hu)).div_const _

/-- This finite-h bound is used only to justify convergence, never as the quantitative final bound. -/
theorem autoSecond_abs_le {n : ℕ} {u : Point n → ℝ} {M : ℝ} (_hM : 0≤ M)
    (hb : ∀ p, |u p|≤ M) (e : Space n) (h : ℝ) (p : Point n) :
    |autoSecond u e h p|≤ 4*M/h^2 := by
  have hNum : |u (p.1+h • e,p.2)+u (p.1-h • e,p.2)-2*u p|≤ 4*M := by
    have htri : |u (p.1+h • e,p.2)+u (p.1-h • e,p.2)-2*u p|≤
        |u (p.1+h • e,p.2)+u (p.1-h • e,p.2)|+|2*u p| := by
      simpa only [sub_zero,zero_sub,abs_neg] using
        abs_sub_le (u (p.1+h • e,p.2)+u (p.1-h • e,p.2)) 0 (2*u p)
    have hsum := abs_add_le (u (p.1+h • e,p.2)) (u (p.1-h • e,p.2))
    have h2 : |2*u p|=2*|u p| := by rw [abs_mul,abs_of_pos (by norm_num : (0 : ℝ)< 2)]
    rw [h2] at htri
    linarith only [htri,hsum,hb (p.1+h • e,p.2),hb (p.1-h • e,p.2),hb p]
  rw [autoSecond,abs_div,abs_of_nonneg (sq_nonneg h)]
  exact div_le_div_of_nonneg_right hNum (sq_nonneg h)

/-- Actual dominated convergence for each fixed nonzero spatial step, with no C2 assumption on w. -/
theorem auto_second_mollifier_energy_tendsto {n : ℕ} (μ : Measure (Point n)) [IsFiniteMeasure μ]
    (w : Point n →ᵇ ℝ) (hw : UniformContinuous (w : Point n → ℝ)) (e : Space n) {h : ℝ} (_hh : h≠0)
    (eps : ℕ → ℝ) (heps : ∀ j, 0< eps j) (hlim : Tendsto eps atTop (𝓝 0)) :
    Tendsto (fun j => ∫ p, (autoSecond (autoSpatialMollify (eps j) (heps j) w) e h p)^2 ∂μ) atTop
      (𝓝 (∫ p, (autoSecond w e h p)^2 ∂μ)) := by
  let D : ℝ := 4*‖w‖/h^2
  have hD : 0≤ D := div_nonneg (mul_nonneg (by norm_num) (norm_nonneg w)) (sq_nonneg h)
  have hUniform := autoSpatialMollify_uniform w hw eps heps hlim
  apply tendsto_integral_of_dominated_convergence (fun _ => D^2)
  · intro j
    exact ((autoSecond_continuous (autoSpatialMollify_continuous (eps j) (heps j) w hw) e h).pow 2).stronglyMeasurable.aestronglyMeasurable
  · exact integrable_const _
  · intro j
    exact ae_of_all μ fun p => by
      have hAbs := autoSecond_abs_le (norm_nonneg w) (autoSpatialMollify_abs_le (eps j) (heps j) w hw) e h p
      have hSq := (sq_le_sq₀ (abs_nonneg _) hD).mpr hAbs
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (autoSecond (autoSpatialMollify (eps j) (heps j) w) e h p))]
      simpa only [sq_abs] using hSq
  · exact ae_of_all μ fun p => by
      have hPlus := hUniform.tendsto_at (p.1+h • e,p.2)
      have hMinus := hUniform.tendsto_at (p.1-h • e,p.2)
      have hCenter := hUniform.tendsto_at p
      have hSecond := ((hPlus.add hMinus).sub (hCenter.const_mul 2)).div_const (h^2)
      simpa only [autoSecond] using hSecond.pow 2

/-- A quantitative energy budget survives the genuine mollifier limit unchanged. -/
theorem auto_second_mollifier_energy_bound {n : ℕ} (μ : Measure (Point n)) [IsFiniteMeasure μ]
    (w : Point n →ᵇ ℝ) (hw : UniformContinuous (w : Point n → ℝ)) (e : Space n) {h : ℝ} (hh : h≠0)
    (eps : ℕ → ℝ) (heps : ∀ j, 0< eps j) (hlim : Tendsto eps atTop (𝓝 0)) {E : ℝ}
    (hb : ∀ j, (∫ p, (autoSecond (autoSpatialMollify (eps j) (heps j) w) e h p)^2 ∂μ)≤ E) :
    (∫ p, (autoSecond w e h p)^2 ∂μ)≤ E :=
  le_of_tendsto_of_tendsto (auto_second_mollifier_energy_tendsto μ w hw e hh eps heps hlim)
    tendsto_const_nhds (Eventually.of_forall hb)

end Yau.LeafProofs.L05AutonomousAux
