import Yau.Proofs.V03EuclideanRadial
import Mathlib.Analysis.Calculus.FDeriv.WithLp

/-! The actual Euclidean norm area is the sum of its scalar component
areas. Native within derivatives justify the formula on the original disc. -/

open scoped Topology ContDiff
open MeasureTheory Filter

noncomputable section
namespace Yau.Blueprint.V03Proof

theorem normDiscArea_eq_closed_integral {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (f : ℂ → H) : normDiscArea f =
      ∫⁻ z in Metric.ball (0 : ℂ) 1, ENNReal.ofReal (2 * ‖closedDiscDerivative f z‖ ^ 2) := by
  apply setLIntegral_congr_fun measurableSet_ball
  intro z hz
  dsimp only
  rw [closedDiscDerivative, fderivWithin_of_mem_nhds
    (mem_of_superset (Metric.isOpen_ball.mem_nhds hz) Metric.ball_subset_closedBall)]

theorem closedDiscDerivative_component {ι : Type*} [Fintype ι]
    {f : ℂ → EuclideanSpace ℂ ι} (hf : ContDiffOn ℂ ∞ f (Metric.closedBall (0 : ℂ) 1))
    {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) 1) (i : ι) :
    closedDiscDerivative (fun w => f w i) z = closedDiscDerivative f z i := by
  have hd := (hasFDerivWithinAt_piLp 2).mp
    (((hf.differentiableOn (by simp)) z hz).hasFDerivWithinAt) i
  have hh := congrArg (fun A : ℂ →L[ℂ] ℂ => A 1)
    (hd.fderivWithin (uniqueDiffOn_complex_closedDisc z hz))
  exact hh

theorem normDiscArea_vector_eq_sum {ι : Type*} [Fintype ι]
    {f : ℂ → EuclideanSpace ℂ ι} (hf : ContDiffOn ℂ ∞ f (Metric.closedBall (0 : ℂ) 1)) :
    normDiscArea f = ∑ i, normDiscArea (fun z => f z i) := by
  classical
  have hfi (i : ι) : ContDiffOn ℂ ∞ (fun z => f z i) (Metric.closedBall (0 : ℂ) 1) :=
    (contDiffOn_piLp 2).mp hf i
  have hm (i : ι) : AEMeasurable
      (fun z => ENNReal.ofReal (2 * ‖closedDiscDerivative (fun w => f w i) z‖ ^ 2))
      (volume.restrict (Metric.ball (0 : ℂ) 1)) := by
    have hc : ContinuousOn
        (fun z => ENNReal.ofReal (2 * ‖closedDiscDerivative (fun w => f w i) z‖ ^ 2))
        (Metric.closedBall (0 : ℂ) 1) :=
      ENNReal.continuous_ofReal.comp_continuousOn
        (continuousOn_const.mul ((continuousOn_closedDiscDerivative (hfi i)).norm.pow 2))
    exact ((hc.mono Metric.ball_subset_closedBall).aestronglyMeasurable measurableSet_ball).aemeasurable
  rw [normDiscArea_eq_closed_integral]
  calc
    _ = ∫⁻ z in Metric.ball (0 : ℂ) 1,
        ∑ i, ENNReal.ofReal (2 * ‖closedDiscDerivative (fun w => f w i) z‖ ^ 2) := by
      apply setLIntegral_congr_fun measurableSet_ball
      intro z hz
      dsimp only
      rw [EuclideanSpace.norm_sq_eq, Finset.mul_sum,
        ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
      apply Finset.sum_congr rfl
      intro i _
      rw [closedDiscDerivative_component hf (Metric.ball_subset_closedBall hz) i]
    _ = ∑ i, ∫⁻ z in Metric.ball (0 : ℂ) 1,
        ENNReal.ofReal (2 * ‖closedDiscDerivative (fun w => f w i) z‖ ^ 2) :=
      lintegral_finsetSum' Finset.univ (fun i _ => hm i)
    _ = _ := Finset.sum_congr rfl (fun i _ => (normDiscArea_eq_closed_integral (fun z => f z i)).symm)

end Yau.Blueprint.V03Proof
