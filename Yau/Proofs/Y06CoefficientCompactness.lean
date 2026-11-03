import Yau.Proofs.Y06ForbiddenProjection

/-! One common subsequence for a countable collection of bounded complex
coefficients; the four polynomial families can be packed into one index. -/

noncomputable section

namespace Yau.Proofs.Y06Aux

open Filter Set
open scoped Topology

theorem common_complex_coefficient_subsequence {ι : Type*} [Countable ι]
    (z : ℕ → ι → ℂ) (B : ι → ℝ) (hbound : ∀ H i, ‖z H i‖ ≤ B i) :
    ∃ (a : ι → ℂ) (subseq : ℕ → ℕ), StrictMono subseq ∧
      Tendsto (fun H => z (subseq H)) atTop (𝓝 a) ∧
      (∀ i, Tendsto (fun H => z (subseq H) i) atTop (𝓝 (a i))) ∧
      ∀ i, ‖a i‖ ≤ B i := by
  let balls : ι → Set ℂ := fun i => Metric.closedBall 0 (max 1 (B i))
  have hcompact : IsCompact (Set.pi univ balls) :=
    isCompact_univ_pi (fun i => isCompact_closedBall _ _)
  have hmem : ∀ H, z H ∈ Set.pi univ balls := by
    intro H i hi
    change z H i ∈ Metric.closedBall 0 (max 1 (B i))
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    exact (hbound H i).trans (le_max_right _ _)
  obtain ⟨a, ha, subseq, hmono, hlim⟩ := hcompact.tendsto_subseq hmem
  have hcoord i : Tendsto (fun H => z (subseq H) i) atTop (𝓝 (a i)) :=
    tendsto_pi_nhds.mp hlim i
  refine ⟨a, subseq, hmono, hlim, hcoord, ?_⟩
  intro i
  exact le_of_tendsto (hcoord i).norm (Eventually.of_forall (fun H => hbound (subseq H) i))

end Yau.Proofs.Y06Aux
