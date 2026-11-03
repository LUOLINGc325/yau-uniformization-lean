import Yau.Proofs.C03EndpointLevi
import Yau.Proofs.E01Matrix

/-! The zero complex direction has a constant planar lower support. -/

noncomputable section
open Filter
open scoped Topology ContDiff

namespace Yau.Proofs.C03Aux
open Yau Yau.Blueprint Yau.NodeProofs.P02Aux Yau.NodeProofs.E01Aux

variable {n : ℕ}

theorem exists_zero_direction_lower_support
    (f : ComplexVector n → ℝ) (z : ComplexVector n) (H : Herm n) (κ : ℝ) :
    ∃ s : ℂ → ℝ, ContDiffAt ℝ 2 s 0 ∧ s 0 = f z ∧
      (∀ᶠ a : ℂ in 𝓝 0, s a ≤ f (z + a • (0 : ComplexVector n))) ∧
      4 * κ * ellipsoidQuadratic H 0 ≤ planarTrace s 0 := by
  refine ⟨fun _ => f z, contDiffAt_const, rfl, ?_, ?_⟩
  · exact Eventually.of_forall (fun a => by simp only [smul_zero, add_zero, le_refl])
  · rw [ellipsoidQuadratic_zero_vector, planarTrace_const]
    simp only [mul_zero, le_refl]

end Yau.Proofs.C03Aux
