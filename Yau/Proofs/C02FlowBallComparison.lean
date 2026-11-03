import Yau.Proofs.C02ShortTimeMetric
import Yau.Proofs.C02LocalBallComparison

/-! The same duration precedes all late times and all compact centres.
The newer unit ball lies in the earlier buffered ball of radius two. -/

noncomputable section
open Set
namespace Yau.Blueprint.C02Proof
variable {n : ℕ} {X : KahlerManifold n}

theorem exists_uniform_flow_ball_comparison
    (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ) (hC01 : HarnackCompleteness X o h)
    (K : Set (Pt X)) (hK : IsCompact K) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ t : ℝ, 2 ≤ t → ∀ p ∈ K,
      ∀ x : Pt X, distFrom (h t) p x ≤ 1 → distFrom (h (t - δ)) p x < 2 := by
  obtain ⟨δ, hδ, hδone, hCompare⟩ := exists_uniform_short_time_metric_comparison
    o h U P ρ hloc hC01 K hK
  refine ⟨δ, hδ, hδone, ?_⟩
  intro t ht p hp x hx
  have ha : 1 ≤ t - δ := by linarith
  let g₀ := completeFlowSlice X o h hloc.1 hC01 (t - δ) (by linarith)
  let g₁ := completeFlowSlice X o h hloc.1 hC01 t (by linarith)
  exact newer_unit_ball_subset_older_two_ball g₀ g₁ p
    (fun y hy v => hCompare (t - δ) ha p hp t ⟨by linarith, by linarith⟩ y hy v) x hx

end Yau.Blueprint.C02Proof
