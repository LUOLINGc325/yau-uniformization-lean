import Yau.LeafProofs.L21WeightedDomainsSmallSolution
import Yau.LeafProofs.L21CompactCoercivity

open MeasureTheory
open scoped ContDiff
noncomputable section
namespace Yau.LeafProofs.L21Aux

/-- Dimension-dependent constants precede the graph coefficients. The
actual weighted maximal complex supplies a small scalar weak solution for
each original column equation, without a domain or solvability premise. -/
theorem weightedDomains_exists_small_column_solutions (n : ℕ) :
    ∃ ε K : ℝ, 0 < ε ∧ 0 < K ∧
      ∀ (A : X n → Matrix (Fin n) (Fin n) ℂ),
        MatrixSmoothOn A (Metric.ball (0 : X n) 2) →
        JetBound 1 ε A (Metric.ball 0 2) → JetBound 2 1 A (Metric.ball 0 2) →
        CommutesOn A (Metric.ball 0 2) → ∀ k : Fin n,
        ∃ u : X n → ℂ, MemLp u 2 (weightedBallMeasure n K) ∧
          LocallyL2On u (Metric.ball 0 1) ∧ DbarWeakOn A u (fun x j => A x j k) (Metric.ball 0 1) ∧
          (∫ x, ‖u x‖^2 ∂weightedBallMeasure n K) ≤
            ∑ j, ∫ x, ‖(rho x : ℂ)*A x j k‖^2 ∂weightedBallMeasure n K := by
  obtain ⟨ε,K,hε,hK,hCoercive⟩ := exists_compact_degenerate_coercivity n
  refine ⟨ε,K,hε,hK,?_⟩
  intro A hA hSmall hJet hMC k
  exact weightedDomains_small_column_solution_of_compact_coercivity K hK.le A hA
    (fun x hx => hMC x (weightedDomains_ball_one_subset_ball_two hx))
    (hCoercive A hA hSmall hJet) k

end Yau.LeafProofs.L21Aux
