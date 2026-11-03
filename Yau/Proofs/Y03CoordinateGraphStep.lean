import Yau.Proofs.Y03SubspaceGraph
import Yau.Proofs.Y03CoordinateInclusion

/-! One explicit extension in a nested coordinate flag. -/

noncomputable section

namespace Yau.Blueprint.Alignment.Y03Proof

open Yau

variable {n : ℕ}


structure CoordinateGraph (s : Finset (Fin n)) (A : Submodule ℂ (ComplexVector n)) (B : ℝ) where
  lift : coordinateSubspace s →L[ℂ] ComplexVector n
  right_inverse : (coordinateProjectionOnto s).comp lift = ContinuousLinearMap.id ℂ (coordinateSubspace s)
  contains : A ≤ LinearMap.range lift.toLinearMap
  norm_bound : ‖lift‖ ≤ B

theorem exists_coordinate_graph_step {s t : Finset (Fin n)} (hst : s ⊆ t)
    (A : Submodule ℂ (ComplexVector n)) (next : coordinateSubspace t →L[ℂ] ComplexVector n)
    (hpnext : (coordinateProjectionOnto t).comp next = ContinuousLinearMap.id ℂ (coordinateSubspace t))
    (hA : A ≤ LinearMap.range next.toLinearMap) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ a : A, ‖a‖ ≤ C * ‖coordinateProjectionOnto s a‖) :
    ∃ L : coordinateSubspace s →L[ℂ] ComplexVector n,
      (coordinateProjectionOnto s).comp L = ContinuousLinearMap.id ℂ (coordinateSubspace s) ∧
      A ≤ LinearMap.range L.toLinearMap ∧
      LinearMap.range L.toLinearMap ≤ LinearMap.range next.toLinearMap ∧ ‖L‖ ≤ C + ‖next‖ := by
  let T := next.comp (coordinateInclusion hst)
  have hT : LinearMap.range T.toLinearMap ≤ LinearMap.range next.toLinearMap := by
    rintro v ⟨e, rfl⟩
    exact ⟨coordinateInclusion hst e, rfl⟩
  have hpT : (coordinateProjectionOnto s).comp T = ContinuousLinearMap.id ℂ (coordinateSubspace s) :=
    restrict_coordinate_graph_right_inverse hst next hpnext
  obtain ⟨L, hpL, hcontains, hrange, hnorm⟩ := exists_subspace_graph_extension (coordinateSubspace s)
    A (LinearMap.range next.toLinearMap) (coordinateProjectionOnto s) T hC hA hpT hT hbound
  refine ⟨L, hpL, hcontains, hrange, ?_⟩
  exact hnorm.trans (add_le_add le_rfl (restrict_coordinate_graph_norm_le hst next))

end Yau.Blueprint.Alignment.Y03Proof
