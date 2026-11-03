import Yau.Proofs.D02DiscEvaluation
import Yau.Proofs.D02Geometry

/-! One actual immersion bound for every original closed holomorphic disc
whose boundary lies in the same compact K. -/

noncomputable section
open scoped Manifold Topology ContDiff
namespace Yau.NodeProofs.D02Aux
open Yau Yau.Blueprint

variable {n N : ℕ} {M : ComplexManifold n}

theorem immersionDisc_differentiableOn {F : M.Carrier → ComplexVector N}
    (hF : IsHolomorphicVecMap F) {f : ℂ → M.Carrier} (hf : IsHolomorphicDisc f) :
    DifferentiableOn ℂ (fun z => F (f z)) (Metric.closedBall (0 : ℂ) 1) := by
  have hF' : MDifferentiableOn (ComplexModel n) (ComplexModel N) F Set.univ := hF.mdifferentiableOn
  exact (hF'.comp (hf.mdifferentiableOn (by simp)) (fun _ _ => Set.mem_univ _)).differentiableOn

theorem vectorDisc_norm_le {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℂ Q]
    {f : ℂ → Q} (hf : DifferentiableOn ℂ f (Metric.closedBall 0 1))
    {B : ℝ} (hB : ∀ ζ : ℂ, ‖ζ‖ = 1 → ‖f ζ‖ ≤ B) :
    ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → ‖f ζ‖ ≤ B := by
  have hcl : DiffContOnCl ℂ f (Metric.ball (0 : ℂ) 1) := by
    refine ⟨hf.mono Metric.ball_subset_closedBall, ?_⟩
    simpa only [closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)] using hf.continuousOn
  intro ζ hζ
  apply Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball hcl ?_ ?_
  · intro w hw
    apply hB w
    simpa only [frontier_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0), Metric.mem_sphere,
      dist_zero_right] using hw
  · simpa only [closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0), Metric.mem_closedBall,
      dist_zero_right] using hζ

theorem immersion_uniformDisc_bound {F : M.Carrier → ComplexVector N}
    (hF : IsHolomorphicVecMap F) {K : Set M.Carrier} (hK : IsCompact K) :
    ∃ B : ℝ, 0 < B ∧ ∀ f : ℂ → M.Carrier, IsHolomorphicDisc f →
      (∀ ζ : ℂ, ‖ζ‖ = 1 → f ζ ∈ K) → ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → ‖F (f ζ)‖ ≤ B := by
  obtain ⟨B, hB⟩ := hK.bddAbove_image hF.continuous.norm.continuousOn
  refine ⟨max B 1, lt_of_lt_of_le zero_lt_one (le_max_right B 1), ?_⟩
  intro f hf hboundary
  apply vectorDisc_norm_le (immersionDisc_differentiableOn hF hf)
  intro ζ hζ
  exact (hB (Set.mem_image_of_mem (fun y => ‖F y‖) (hboundary ζ hζ))).trans (le_max_left B 1)

end Yau.NodeProofs.D02Aux
