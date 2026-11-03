import Yau.Proofs.V03LogTrace
import Yau.Proofs.V03Radial

/-! Local continuity of closed-disc derivatives and the actual angular
chain rule, including on the unit circle. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder
open Filter

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

theorem uniqueDiffOn_real_closedDisc : UniqueDiffOn ℝ (Metric.closedBall (0 : ℂ) 1) :=
  uniqueDiffOn_convex (convex_closedBall (0 : ℂ) 1) (by
    rw [interior_closedBall (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)]
    exact ⟨0, by simp⟩)

theorem continuousWithinAt_fderivWithin_closedDisc {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : ℂ → F} {z : ℂ}
    (hz : z ∈ Metric.closedBall 0 1)
    (hf : ContDiffWithinAt ℝ 2 f (Metric.closedBall 0 1) z) :
    ContinuousWithinAt (fderivWithin ℝ f (Metric.closedBall 0 1)) (Metric.closedBall 0 1) z := by
  obtain ⟨V, hV, hzV, hfV⟩ := hf.contDiffOn' (m := 1) (by norm_num) (by norm_num)
  rw [Set.insert_eq_of_mem hz] at hfV
  have hu : UniqueDiffOn ℝ (Metric.closedBall (0 : ℂ) 1 ∩ V) :=
    uniqueDiffOn_real_closedDisc.inter hV
  have hD := hfV.continuousOn_fderivWithin hu (by simp)
  apply (continuousWithinAt_inter (hV.mem_nhds hzV)).mp
  apply (hD z ⟨hz, hzV⟩).congr_of_eventuallyEq_of_mem ?_ ⟨hz, hzV⟩
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact (fderivWithin_inter (hV.mem_nhds hy.2)).symm

theorem hasDerivAt_circlePoint (θ : ℝ) :
    HasDerivAt circlePoint (circlePoint θ * Complex.I) θ := by
  have heq : circlePoint = circleMap (0 : ℂ) 1 := by
    funext t
    simp [circlePoint, circleMap]
  rw [heq]
  exact hasDerivAt_circleMap (0 : ℂ) 1 θ

def angularWithinDerivative (f : ℂ → ℝ) (r θ : ℝ) : ℝ :=
  fderivWithin ℝ f (Metric.closedBall 0 1) ((r : ℂ) * circlePoint θ)
    ((r : ℂ) * (circlePoint θ * Complex.I))

theorem hasDerivAt_radial_trace {f : ℂ → ℝ} {r θ : ℝ}
    (hr : r ∈ Set.Icc (0 : ℝ) 1)
    (hf : DifferentiableWithinAt ℝ f (Metric.closedBall 0 1) ((r : ℂ) * circlePoint θ)) :
    HasDerivAt (fun t => f ((r : ℂ) * circlePoint t)) (angularWithinDerivative f r θ) θ := by
  have hc := (hasDerivAt_circlePoint θ).const_mul (r : ℂ)
  have hh := hf.hasFDerivWithinAt.comp_hasDerivAt θ hc
    (Eventually.of_forall (fun t => radial_maps_closedBall hr.1 hr.2 (circlePoint_mem_closedBall t)))
  exact hh

theorem angularWithinDerivative_continuousWithinAt {f : ℂ → ℝ} (θ : ℝ)
    (hf : ContDiffWithinAt ℝ 2 f (Metric.closedBall 0 1) (circlePoint θ)) :
    ContinuousWithinAt (fun p : ℝ × ℝ => angularWithinDerivative f p.1 p.2)
      (Set.Icc 0 1 ×ˢ Set.univ) (1, θ) := by
  have hD := continuousWithinAt_fderivWithin_closedDisc (circlePoint_mem_closedBall θ) hf
  have hm : Continuous (fun p : ℝ × ℝ => (p.1 : ℂ) * circlePoint p.2) :=
    (Complex.continuous_ofReal.comp continuous_fst).mul
      (circlePoint_contDiff.continuous.comp continuous_snd)
  have hmap : Set.MapsTo (fun p : ℝ × ℝ => (p.1 : ℂ) * circlePoint p.2)
      (Set.Icc 0 1 ×ˢ Set.univ) (Metric.closedBall 0 1) :=
    fun p hp => radial_maps_closedBall hp.1.1 hp.1.2 (circlePoint_mem_closedBall p.2)
  have hD' : ContinuousWithinAt (fderivWithin ℝ f (Metric.closedBall 0 1))
      (Metric.closedBall 0 1) ((1 : ℂ) * circlePoint θ) := by simpa only [one_mul] using hD
  have hDC := ContinuousWithinAt.comp
    (f := fun p : ℝ × ℝ => (p.1 : ℂ) * circlePoint p.2) (x := ((1 : ℝ), θ))
    hD' hm.continuousWithinAt hmap
  have hv : Continuous (fun p : ℝ × ℝ => (p.1 : ℂ) * (circlePoint p.2 * Complex.I)) :=
    (Complex.continuous_ofReal.comp continuous_fst).mul
      ((circlePoint_contDiff.continuous.comp continuous_snd).mul continuous_const)
  simpa only [angularWithinDerivative, Function.comp_def] using hDC.clm_apply hv.continuousWithinAt

end Yau.Blueprint.V03Proof
