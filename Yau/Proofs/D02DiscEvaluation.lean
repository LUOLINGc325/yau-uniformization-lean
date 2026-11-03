import Yau.Proofs.D02FieldHolomorphic
import Yau.Proofs.V03DiscSmooth

/-! Scalar evaluation on the original within-at closed-disc regularity. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder
open Filter

noncomputable section
namespace Yau.NodeProofs.D02Aux
open Yau Yau.Blueprint Yau.Blueprint.V03Proof

variable {n : ℕ} {M : ComplexManifold n}

/-- A scalar holomorphic in the induced atlas pulls back to a genuine scalar disc. -/
theorem cotangentDisc_scalar_differentiableOn {f : ℂ → CotangentPoint M}
    (hf : CotangentDisc f) {b : CotangentPoint M → ℂ}
    (hb : ∀ x, DifferentiableOn ℂ (fun p => b (cotangentChartInv x p)) (cotangentTarget x)) :
    DifferentiableOn ℂ (fun ζ => b (f ζ)) (Metric.closedBall 0 1) := by
  intro ζ hζ
  obtain ⟨V, hV, hζV, hsource, hcoord⟩ := (cotangentDisc_holomorphicOn hf).2 ζ hζ
  have hmodel := (hb (f ζ).1).comp (hcoord.differentiableOn (by simp))
    (fun η hη => cotangentChart_mapsTo (f ζ).1 (hsource η hη))
  apply (differentiableWithinAt_inter (hV.mem_nhds hζV)).mp
  apply (hmodel ζ ⟨hζ, hζV⟩).congr_of_eventuallyEq_of_mem ?_ ⟨hζ, hζV⟩
  filter_upwards [self_mem_nhdsWithin] with η hη
  exact congrArg b (cotangentChart_left_inv (f ζ).1 (hsource η hη)).symm

theorem cotangentDisc_fieldEvaluation_differentiableOn {f : ℂ → CotangentPoint M}
    (hf : CotangentDisc f) {V : VectorField M} (hV : IsHolomorphicField V) :
    DifferentiableOn ℂ (fun ζ => fieldEvaluation V (f ζ)) (Metric.closedBall 0 1) :=
  cotangentDisc_scalar_differentiableOn hf (fieldEvaluation_differentiableOn_chart hV)

/-- The scalar maximum principle uses only interior holomorphicity and closed-disc continuity. -/
theorem scalarDisc_norm_le {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (Metric.closedBall 0 1))
    {C : ℝ} (hC : ∀ ζ : ℂ, ‖ζ‖ = 1 → ‖f ζ‖ ≤ C) :
    ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → ‖f ζ‖ ≤ C := by
  have hcl : DiffContOnCl ℂ f (Metric.ball (0 : ℂ) 1) := by
    refine ⟨?_, ?_⟩
    · exact hf.mono Metric.ball_subset_closedBall
    · simpa only [closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)] using hf.continuousOn
  intro ζ hζ
  apply Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball hcl ?_ ?_
  · intro w hw
    apply hC w
    simpa only [frontier_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0), Metric.mem_sphere,
      dist_zero_right] using hw
  · simpa only [closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0), Metric.mem_closedBall,
      dist_zero_right] using hζ

/-- The same one boundary bound controls every interior evaluation of every disc. -/
theorem cotangentDisc_fieldEvaluation_norm_le {f : ℂ → CotangentPoint M}
    (hf : CotangentDisc f) {V : VectorField M} (hV : IsHolomorphicField V)
    {C : ℝ} (hC : ∀ ζ : ℂ, ‖ζ‖ = 1 → ‖fieldEvaluation V (f ζ)‖ ≤ C) :
    ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → ‖fieldEvaluation V (f ζ)‖ ≤ C :=
  scalarDisc_norm_le (cotangentDisc_fieldEvaluation_differentiableOn hf hV) hC

end Yau.NodeProofs.D02Aux
