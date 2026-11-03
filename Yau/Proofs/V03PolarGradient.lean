import Yau.Proofs.V03BoundaryDerivative

/-! The actual closed-disc gradient supplies smooth polar fluxes on the
whole closed radial rectangle. No extension of the disc is asserted. -/

open scoped Topology ContDiff
open Filter

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

def polarDiscPoint (p : ℝ × ℝ) : ℂ := (p.1 : ℂ) * circlePoint p.2

theorem polarDiscPoint_contDiff : ContDiff ℝ ∞ polarDiscPoint :=
  (Complex.ofRealCLM.contDiff.comp contDiff_fst).mul (circlePoint_contDiff.comp contDiff_snd)

theorem polarDiscPoint_norm (p : ℝ × ℝ) : ‖polarDiscPoint p‖ = |p.1| := by
  simp [polarDiscPoint, norm_mul, circlePoint_norm]

theorem polarDiscPoint_mem_closedDisc {p : ℝ × ℝ} (hp : p.1 ∈ Set.Icc 0 1) :
    polarDiscPoint p ∈ Metric.closedBall (0 : ℂ) 1 := by
  rw [Metric.mem_closedBall, dist_zero_right, polarDiscPoint_norm, abs_of_nonneg hp.1]
  exact hp.2

theorem polarDiscPoint_mem_ball {p : ℝ × ℝ} (hp : p.1 ∈ Set.Ioo 0 1) :
    polarDiscPoint p ∈ Metric.ball (0 : ℂ) 1 := by
  rw [Metric.mem_ball, dist_zero_right, polarDiscPoint_norm, abs_of_pos hp.1]
  exact hp.2

def closedRealGradient (u : ℂ → ℝ) (z : ℂ) : ℂ →L[ℝ] ℝ :=
  fderivWithin ℝ u (Metric.closedBall 0 1) z

theorem closedRealGradient_contDiffOn {u : ℂ → ℝ}
    (hu : ContDiffOn ℝ ∞ u (Metric.closedBall (0 : ℂ) 1)) :
    ContDiffOn ℝ ∞ (closedRealGradient u) (Metric.closedBall (0 : ℂ) 1) :=
  hu.fderivWithin uniqueDiffOn_real_closedDisc (m := ∞) (by simp)

theorem closedRealGradient_eventually_eq {u : ℂ → ℝ} {z : ℂ}
    (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    closedRealGradient u =ᶠ[𝓝 z] fderiv ℝ u := by
  filter_upwards [Metric.isOpen_ball.mem_nhds hz] with z' hz'
  exact fderivWithin_of_mem_nhds (mem_of_superset (Metric.isOpen_ball.mem_nhds hz')
    Metric.ball_subset_closedBall)

def polarRadialFlux (u : ℂ → ℝ) (p : ℝ × ℝ) : ℝ :=
  p.1 * closedRealGradient u (polarDiscPoint p) (circlePoint p.2)

def polarAngularFlux (u : ℂ → ℝ) (p : ℝ × ℝ) : ℝ :=
  closedRealGradient u (polarDiscPoint p) (circlePoint p.2 * Complex.I)

theorem polarRadialFlux_contDiffOn {u : ℂ → ℝ}
    (hu : ContDiffOn ℝ ∞ u (Metric.closedBall (0 : ℂ) 1)) :
    ContDiffOn ℝ ∞ (polarRadialFlux u) (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ) := by
  have hD : ContDiffOn ℝ ∞ (fun p => closedRealGradient u (polarDiscPoint p))
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ) :=
    (closedRealGradient_contDiffOn hu).comp polarDiscPoint_contDiff.contDiffOn
      (fun p hp => polarDiscPoint_mem_closedDisc hp.1)
  exact contDiffOn_fst.mul (hD.clm_apply (circlePoint_contDiff.comp contDiff_snd).contDiffOn)

theorem polarAngularFlux_contDiffOn {u : ℂ → ℝ}
    (hu : ContDiffOn ℝ ∞ u (Metric.closedBall (0 : ℂ) 1)) :
    ContDiffOn ℝ ∞ (polarAngularFlux u) (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ) := by
  have hD : ContDiffOn ℝ ∞ (fun p => closedRealGradient u (polarDiscPoint p))
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ) :=
    (closedRealGradient_contDiffOn hu).comp polarDiscPoint_contDiff.contDiffOn
      (fun p hp => polarDiscPoint_mem_closedDisc hp.1)
  exact hD.clm_apply (((circlePoint_contDiff.comp contDiff_snd).mul contDiff_const).contDiffOn)

theorem polarRadialFlux_eventually_eq {u : ℂ → ℝ} {p : ℝ × ℝ}
    (hp : p.1 ∈ Set.Ioo 0 1) :
    polarRadialFlux u =ᶠ[𝓝 p] (fun p' => p'.1 * fderiv ℝ u (polarDiscPoint p') (circlePoint p'.2)) := by
  have hh := (closedRealGradient_eventually_eq (u := u) (polarDiscPoint_mem_ball hp)).comp_tendsto
    polarDiscPoint_contDiff.continuous.continuousAt
  filter_upwards [hh] with p' hp'
  exact congrArg (fun A : ℂ →L[ℝ] ℝ => p'.1 * A (circlePoint p'.2)) hp'

theorem polarAngularFlux_eventually_eq {u : ℂ → ℝ} {p : ℝ × ℝ}
    (hp : p.1 ∈ Set.Ioo 0 1) :
    polarAngularFlux u =ᶠ[𝓝 p]
      (fun p' => fderiv ℝ u (polarDiscPoint p') (circlePoint p'.2 * Complex.I)) := by
  have hh := (closedRealGradient_eventually_eq (u := u) (polarDiscPoint_mem_ball hp)).comp_tendsto
    polarDiscPoint_contDiff.continuous.continuousAt
  filter_upwards [hh] with p' hp'
  exact congrArg (fun A : ℂ →L[ℝ] ℝ => A (circlePoint p'.2 * Complex.I)) hp'

end Yau.Blueprint.V03Proof
