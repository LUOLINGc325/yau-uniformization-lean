import Yau.Proofs.V03PolarDifferential
import Yau.Proofs.V03PolarGreenFlux
import Yau.Proofs.V03PolarDiscIntegral
import Yau.Proofs.V03ClosedLaplacian

/-! Green's formula for the genuine Laplacian of a smooth closed disc.
All endpoint values are the native within derivatives of the original map. -/

open scoped Topology ContDiff
open MeasureTheory Filter

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

theorem closedPolarDivergence_eq_laplacian {u : ℂ → ℝ}
    (hu : ContDiffOn ℝ ∞ u (Metric.closedBall (0 : ℂ) 1))
    {p : ℝ × ℝ} (hp : p.1 ∈ Set.Ioo 0 1) :
    closedPolarDivergence u p = p.1 * closedLaplacian u (polarDiscPoint p) := by
  have hnhds : Set.Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set ℝ) ∈ 𝓝 p :=
    prod_mem_nhds (Icc_mem_nhds hp.1 hp.2) univ_mem
  have huAt : ContDiffAt ℝ 2 u (polarDiscPoint p) :=
    (hu.contDiffAt (mem_of_superset
      (Metric.isOpen_ball.mem_nhds (polarDiscPoint_mem_ball hp)) Metric.ball_subset_closedBall)).of_le (by simp)
  rw [closedPolarDivergence, fderivWithin_of_mem_nhds hnhds, fderivWithin_of_mem_nhds hnhds,
    polarFlux_divergence hp huAt, closedLaplacian_eq (polarDiscPoint_mem_ball hp)]

theorem integral_closedLaplacian_eq_boundary {u : ℂ → ℝ}
    (hu : ContDiffOn ℝ ∞ u (Metric.closedBall (0 : ℂ) 1)) :
    (∫ z in Metric.ball (0 : ℂ) 1, closedLaplacian u z) =
      ∫ θ in (-Real.pi)..Real.pi, closedRealGradient u (circlePoint θ) (circlePoint θ) := by
  have hleft : (∫ r in (0 : ℝ)..1, ∫ θ in (-Real.pi)..Real.pi, closedPolarDivergence u (r, θ)) =
      ∫ r in (0 : ℝ)..1, ∫ θ in (-Real.pi)..Real.pi, r * closedLaplacian u (polarDiscPoint (r, θ)) := by
    simp only [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      integral_Ioc_eq_integral_Ioo]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    apply intervalIntegral.integral_congr
    intro θ _
    exact closedPolarDivergence_eq_laplacian hu hr
  calc
    _ = ∫ r in (0 : ℝ)..1, ∫ θ in (-Real.pi)..Real.pi, r * closedLaplacian u (polarDiscPoint (r, θ)) :=
      integral_unitDisc_eq_polar (closedLaplacian_contDiffOn hu).continuousOn
    _ = _ := hleft.symm.trans (polarGreen_flux hu)

end Yau.Blueprint.V03Proof
