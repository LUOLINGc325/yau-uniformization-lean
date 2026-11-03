import spec.CHAIN.CONTRACTS
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Differentiation over the compact radial parameter interval, with the
dominating bound extracted from genuine joint continuity on a compact set. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Interval Topology
namespace Yau.Blueprint.C02Proof
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem hasFDerivAt_intervalIntegral_of_joint_continuity
    (G : E → ℝ → F) (G' : E → ℝ → E →L[ℝ] F)
    (hG : Continuous (Function.uncurry G)) (hG' : Continuous (Function.uncurry G'))
    (hDeriv : ∀ x t, HasFDerivAt (fun y => G y t) (G' x t) x) (x : E) :
    HasFDerivAt (fun y => ∫ t in (0 : ℝ)..1, G y t)
      (∫ t in (0 : ℝ)..1, G' x t) x := by
  let : ProperSpace E := FiniteDimensional.proper ℝ E
  have hCompact : IsCompact (Metric.closedBall x 1 ×ˢ Icc (0 : ℝ) 1) :=
    (isCompact_closedBall x 1).prod isCompact_Icc
  have hNorm : Continuous (fun p : E × ℝ => ‖G' p.1 p.2‖) := hG'.norm
  obtain ⟨C, hC⟩ := hCompact.bddAbove_image hNorm.continuousOn
  have hBound (y : E) (hy : y ∈ Metric.closedBall x 1)
      (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : ‖G' y t‖ ≤ C :=
    hC (mem_image_of_mem (fun p : E × ℝ => ‖G' p.1 p.2‖) (show (y, t) ∈
      Metric.closedBall x 1 ×ˢ Icc (0 : ℝ) 1 from ⟨hy, ht⟩))
  have hGI (y : E) : IntervalIntegrable (G y) volume 0 1 :=
    (hG.comp (continuous_const.prodMk continuous_id)).intervalIntegrable 0 1
  have hG'I (y : E) : IntervalIntegrable (G' y) volume 0 1 :=
    (hG'.comp (continuous_const.prodMk continuous_id)).intervalIntegrable 0 1
  apply intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (s := Metric.ball x 1) (bound := fun _ => C) (Metric.ball_mem_nhds x zero_lt_one)
  · exact Eventually.of_forall (fun y => (hGI y).aestronglyMeasurable_restrict_uIoc)
  · exact hGI x
  · exact (hG'I x).aestronglyMeasurable_restrict_uIoc
  · apply Eventually.of_forall
    intro t ht y hy
    rw [uIoc_of_le zero_le_one] at ht
    exact hBound y (Metric.mem_closedBall.mpr (Metric.mem_ball.mp hy).le) t ⟨ht.1.le, ht.2⟩
  · exact intervalIntegrable_const
  · exact Eventually.of_forall (fun t _ y _ => hDeriv y t)

end Yau.Blueprint.C02Proof
