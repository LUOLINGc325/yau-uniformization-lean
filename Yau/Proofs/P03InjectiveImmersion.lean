import Yau.Proofs.P03FiniteScalarImmersion
import Yau.Proofs.P03ScalarInterpolation

noncomputable section

namespace Yau.NodeProofs.P03Aux

/-- The third original P03 conjunct for the actual given Kähler manifold. -/
theorem finite_holomorphic_injective_immersion {n : ℕ} (X : KahlerManifold n) :
    ∃ (N : ℕ) (F : X.manifold.Carrier → ComplexVector N),
      IsHolomorphicVecMap F ∧ Function.Injective F ∧ IsImmersionMap F := by
  obtain ⟨F, hF, hinj, himm⟩ := finite_injective_immersion_of_scalar_jets X.manifold
    (scalar_finite_interpolation X)
  exact ⟨2 * n + 1, F, hF, hinj, himm⟩

end Yau.NodeProofs.P03Aux
