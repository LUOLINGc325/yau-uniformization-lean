import Yau.LeafProofs.L21WeightedDomainsNorms

open MeasureTheory Filter Set
open scoped Topology ContDiff InnerProductSpace
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ}

theorem weightedDomains_ball_one_subset_ball_two :
    Metric.ball (0 : X n) 1 ⊆ Metric.ball 0 2 :=
  Metric.ball_subset_ball (by norm_num)

theorem weightedDomains_closedBall_one_subset_ball_two :
    Metric.closedBall (0 : X n) 1 ⊆ Metric.ball 0 2 := by
  intro x hx
  exact Metric.mem_ball.mpr (lt_of_le_of_lt (Metric.mem_closedBall.mp hx) (by norm_num))

theorem weightedDomains_finite_principal_bound {α β ι : Type*}
    [Fintype α] [Fintype β] [Fintype ι]
    (p : β → α → ι → X n → ℂ)
    (hp : ∀ r c i, ContinuousOn (p r c i) (Metric.ball 0 2)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r c i x, x ∈ Metric.ball (0 : X n) 1 → ‖p r c i x‖ ≤ C := by
  classical
  have hCompact := isCompact_closedBall (0 : X n) (1 : ℝ)
  choose C hC using fun r c i => hCompact.exists_bound_of_continuousOn
    ((hp r c i).mono weightedDomains_closedBall_one_subset_ball_two)
  refine ⟨∑ r, ∑ c, ∑ i, max 0 (C r c i),?_,?_⟩
  · positivity
  · intro r c i x hx
    calc
      ‖p r c i x‖ ≤ C r c i := hC r c i x (Metric.ball_subset_closedBall hx)
      _ ≤ max 0 (C r c i) := le_max_right _ _
      _ ≤ ∑ j, max 0 (C r c j) := Finset.single_le_sum (fun j _ => le_max_left _ _) (Finset.mem_univ i)
      _ ≤ ∑ d, ∑ j, max 0 (C r d j) := Finset.single_le_sum
        (f := fun d => ∑ j, max 0 (C r d j)) (fun d _ => by positivity) (Finset.mem_univ c)
      _ ≤ ∑ s, ∑ d, ∑ j, max 0 (C s d j) := Finset.single_le_sum
        (f := fun s => ∑ d, ∑ j, max 0 (C s d j)) (fun s _ => by positivity) (Finset.mem_univ r)

theorem weightedDomains_matrixSmoothOn_ball_one
    {A : X n → Matrix (Fin n) (Fin n) ℂ} (hA : MatrixSmoothOn A (Metric.ball 0 2)) :
    MatrixSmoothOn A (Metric.ball 0 1) :=
  fun i j => (hA i j).mono weightedDomains_ball_one_subset_ball_two

end Yau.LeafProofs.L21Aux
