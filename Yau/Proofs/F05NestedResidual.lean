import Yau.Proofs.F05NestedCutoffs
import Yau.Proofs.F05OuterResidual

/-! The actual nested cutoff is identically one on both pieces of the
outer residual. No native commutator or extra cutoff factor is discarded. -/

open Set
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1800000
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem F05OuterResidual_zero_outside (a : Point n → Mat n) (b : Point n → RIdx n → ℝ)
    (β : Space n → ℝ) (W H : Point n → ℝ) {p : Point n} (hp : p.1 ∉ tsupport β) :
    F05OuterResidual a b β W H p = 0 := by
  have hV := image_eq_zero_of_notMem_tsupport hp
  have hD := fderiv_of_notMem_tsupport (𝕜 := ℝ) hp
  have hDD := fderiv_of_notMem_tsupport (𝕜 := ℝ)
    (show p.1 ∉ tsupport (fderiv ℝ β) from fun h => hp (tsupport_fderiv_subset ℝ h))
  simp only [F05OuterResidual,spatialCutoffCommutator,hV,hD,hDD,zero_apply,
    zero_mul,mul_zero,add_zero,Finset.sum_const_zero]

theorem F05_nested_model_cutoff_one {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (i : Fin A.count) {β γ : M.Carrier → ℝ}
    (hβ : tsupport β ⊆ lift A i '' Metric.closedBall 0 (5/8))
    (hγ : tsupport γ ⊆ lift A i '' Metric.closedBall 0 (3/4))
    (hOne : ∀ z ∈ Metric.closedBall (0 : Space n) (5/8), γ (lift A i z) = 1)
    {z : Space n} (hz : z ∈ tsupport (F05ModelOuterCutoff A i β)) :
    F05ModelOuterCutoff A i γ z = 1 := by
  have hBall := F05ModelOuterCutoff_tsupport_radius hA i (by norm_num : (5/8 : ℝ) < 3) hβ hz
  rw [F05ModelOuterCutoff_eq hA i hγ (Metric.closedBall_subset_ball (by norm_num : (5/8 : ℝ) < 3) hBall)]
  exact hOne z hBall

theorem F05_nested_residual_product {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (i : Fin A.count) {β γ : M.Carrier → ℝ}
    (hβ : tsupport β ⊆ lift A i '' Metric.closedBall 0 (5/8))
    (hγ : tsupport γ ⊆ lift A i '' Metric.closedBall 0 (3/4))
    (hOne : ∀ z ∈ Metric.closedBall (0 : Space n) (5/8), γ (lift A i z) = 1)
    (a : Point n → Mat n) (b : Point n → RIdx n → ℝ) (W H : Point n → ℝ)
    (p : Point n) : F05ModelOuterCutoff A i γ p.1 *
      F05OuterResidual a b (F05ModelOuterCutoff A i β) W H p =
        F05OuterResidual a b (F05ModelOuterCutoff A i β) W H p := by
  by_cases hp : p.1 ∈ tsupport (F05ModelOuterCutoff A i β)
  · rw [F05_nested_model_cutoff_one hA i hβ hγ hOne hp,one_mul]
  · rw [F05OuterResidual_zero_outside a b (F05ModelOuterCutoff A i β) W H hp,mul_zero]

end Yau.Proofs.F05Aux
