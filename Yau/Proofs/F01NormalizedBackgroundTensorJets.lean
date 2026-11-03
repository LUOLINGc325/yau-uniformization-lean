import Yau.Proofs.F01DilatedAffineTensorHolder
import Yau.Proofs.F01NormalizedComplexFlowMatrix

/-! The actual normalized complex background has one all-order family
of Holder budgets, before every chart center and every admissible scale.
The fixed background tensors and Ricci tensors supply the next jets. -/
noncomputable section
open Set Metric
open scoped ContDiff Matrix Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

theorem normalized_background_spatial_tensor_holder_budgets
    (A : BoundedChartFamily g) {β : ℝ} (hβ : β ≤ 1) :
    ∃ K : ℕ → ℝ, (∀ k, 0 < K k) ∧
      ∀ k (ρ : ℝ), 0 < ρ → ρ ≤ A.radius → ρ ≤ 1 → ∀ a : M.Carrier,
      HolderBound β (cylinder (ball (0 : Space n) 1) (-1) 1)
        (fun p => iteratedFDeriv ℝ k (fun z => normalizedComplexBackground A a ρ (z, p.2)) p.1)
        (K k) := by
  have hex : ∀ k : ℕ, ∃ K : ℝ, 0 < K ∧
      ∀ (ρ : ℝ), 0 < ρ → ρ ≤ A.radius → ρ ≤ 1 → ∀ a : M.Carrier,
      HolderBound β (cylinder (ball (0 : Space n) 1) (-1) 1)
        (fun p => iteratedFDeriv ℝ k (fun z => normalizedComplexBackground A a ρ (z, p.2)) p.1) K := by
    intro k
    obtain ⟨K, hK, hk⟩ := dilated_affine_spatial_tensor_holder_budget k
      (background_matrix_frobenius_uniform_jets A (k + 1))
      (backgroundRicci_frobenius_uniform_jets A (k + 1))
      (background_matrix_frobenius_smooth A) (backgroundRicci_frobenius_smooth A) hβ
    refine ⟨K, hK, ?_⟩
    intro ρ hρ hρr hρ1 a
    apply hk ρ hρ hρr hρ1 (-(ρ ^ 2)) ?_ a
    rw [abs_neg, abs_of_nonneg (sq_nonneg _)]
    nlinarith
  choose K hK hk using hex
  exact ⟨K, hK, hk⟩

end Yau.NodeProofs.F01Aux
