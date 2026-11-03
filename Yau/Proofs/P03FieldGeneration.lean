import Yau.Proofs.P03FiniteGlobalFields
import Yau.Proofs.P03FieldInterpolation

noncomputable section

namespace Yau.NodeProofs.P03Aux

/-- The fourth original P03 conjunct, with one finite global holomorphic
field tuple chosen before every point and the actual intrinsic fibre span. -/
theorem field_finite_generation {n : ℕ} (X : KahlerManifold n) :
    ∃ (m : ℕ) (V : Fin m → VectorField X.manifold),
      (∀ i, IsHolomorphicField (V i)) ∧
      ∀ x, Submodule.span ℂ (Set.range fun i => V i x) = ⊤ := by
  obtain ⟨V, hV, hspan⟩ := finite_spanning_tuple_of_field_jets X.manifold
    (field_finite_interpolation X)
  exact ⟨2 * n, V, hV, hspan⟩

end Yau.NodeProofs.P03Aux
