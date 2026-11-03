import Yau.Proofs.V03CompactFiber
import Yau.Proofs.V03LogTrace
import Yau.Proofs.V03Radial

/-! Uniform radial convergence of an actual boundary trace only needs
within-disc continuity at its circle, without an extension across the circle. -/

open scoped Topology
open Filter

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

theorem radial_trace_tendstoUniformlyOn {F : Type*} [PseudoMetricSpace F] {b : ℂ → F}
    (hb : ∀ θ, ContinuousWithinAt b (Metric.closedBall 0 1) (circlePoint θ)) :
    TendstoUniformlyOn (fun r : ℝ => fun θ => b ((r : ℂ) * circlePoint θ))
      (fun θ => b (circlePoint θ)) (𝓝[Set.Icc 0 1] 1) (Set.Icc 0 (2 * Real.pi)) := by
  have hm : Continuous (fun p : ℝ × ℝ => (p.1 : ℂ) * circlePoint p.2) :=
    (Complex.continuous_ofReal.comp continuous_fst).mul
      (circlePoint_contDiff.continuous.comp continuous_snd)
  have hmap : Set.MapsTo (fun p : ℝ × ℝ => (p.1 : ℂ) * circlePoint p.2)
      (Set.Icc 0 1 ×ˢ Set.univ) (Metric.closedBall 0 1) :=
    fun p hp => radial_maps_closedBall hp.1.1 hp.1.2 (circlePoint_mem_closedBall p.2)
  have hA (θ : ℝ) : ContinuousWithinAt (fun p : ℝ × ℝ => b ((p.1 : ℂ) * circlePoint p.2))
      (Set.Icc 0 1 ×ˢ Set.univ) (1, θ) := by
    have hc := ContinuousWithinAt.comp_of_eq
      (f := fun p : ℝ × ℝ => (p.1 : ℂ) * circlePoint p.2) (x := ((1 : ℝ), θ))
      (hb θ) hm.continuousWithinAt hmap (by simp)
    simpa only [Function.comp_def] using hc
  have hbase : Continuous (fun θ => b (circlePoint θ)) := by
    rw [continuous_iff_continuousAt]
    intro θ
    have hc := ContinuousWithinAt.comp (f := circlePoint) (x := θ) (s := Set.univ)
      (hb θ) circlePoint_contDiff.continuous.continuousWithinAt
      (fun t _ => circlePoint_mem_closedBall t)
    simpa only [ContinuousAt, ContinuousWithinAt, Function.comp_def, nhdsWithin_univ] using hc
  have hbase1 : Continuous (fun θ => b (((1 : ℝ) : ℂ) * circlePoint θ)) := by
    simpa only [Complex.ofReal_one, one_mul] using hbase
  have ht := tendstoUniformlyOn_of_continuousWithinAt_fiber
    (K := Set.Icc 0 (2 * Real.pi))
    (A := fun r : ℝ => fun θ => b ((r : ℂ) * circlePoint θ)) isCompact_Icc
    (fun θ _ => hA θ) (fun θ _ => hbase1.continuousAt)
  simpa only [Complex.ofReal_one, one_mul] using ht

end Yau.Blueprint.V03Proof
