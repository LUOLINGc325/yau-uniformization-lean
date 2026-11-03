import Yau.Proofs.F01CoefficientExtensions
import Yau.Proofs.F01FiniteBudgets

/-! One all-orders sequence bounds every matrix entry of the actual
rescaled coefficient, before center, scale, and coordinate are chosen. -/
open Set Metric
open scoped ContDiff
noncomputable section
namespace Yau.NodeProofs.F01Aux
variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype ι]

theorem actual_coefficient_all_entry_derivative_budgets (b : E) {r c L M : ℝ}
    (hr : 0 < r) (hc : 0 ≤ c) (hcr : c ≤ r / 12) (hL : 0 < L) (hM : 0 ≤ M)
    {u : E → ℝ} {G : E → Matrix ι ι ℂ}
    (hu : ContDiffOn ℝ ∞ u (ball b (4 * r)))
    (hG : ∀ i j, ContDiffOn ℝ ∞ (fun y => G y i j) (ball b (4 * r)))
    (hD : ∀ y ∈ ball b (4 * r), ‖fderiv ℝ u y‖ ≤ M)
    (hbudget : 2 * c * M / L ≤ 1 / 2) :
    ∃ C : ℕ → ℝ, (∀ k, 0 < C k) ∧ ∀ k z₀ δ z,
      z₀ ∈ closedBall b r → 0 < δ → δ ≤ 1 → 1 - u z₀ / L = δ → z ∈ ball (0 : E) 1 →
      ∀ i j, ‖iteratedFDeriv ℝ k
        (fun w => interiorExtension u (fun y => G y i j) L c (z₀, δ, w)) z‖ ≤ C k := by
  classical
  have hentries := fun p : ι × ι => actual_coefficient_all_derivative_budgets b
    hr hc hcr hL hM hu (hG p.1 p.2) hD hbudget
  choose C hC hbound using hentries
  obtain ⟨B, hB, hCB, _⟩ := exists_finite_uniform_budgets (Finset.univ : Finset (ι × ι)) C (fun _ => 0)
  refine ⟨B, hB, ?_⟩
  intro k z₀ δ z hz₀ hδ hδ1 hbase hz i j
  exact (hbound (i, j) k z₀ δ z hz₀ hδ hδ1 hbase hz).trans
    (hCB (i, j) (Finset.mem_univ _) k)

end Yau.NodeProofs.F01Aux
