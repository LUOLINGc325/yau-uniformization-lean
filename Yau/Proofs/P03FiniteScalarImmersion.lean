import Yau.Proofs.P03SimultaneousScalarTuple
import Yau.Proofs.P03ScalarTupleGeometry

open scoped Manifold Topology

noncomputable section

namespace Yau.NodeProofs.P03Aux

/-- The original scalar interpolation clause gives one finite-dimensional
holomorphic injective immersion, chosen before all points and tangent vectors. -/
theorem finite_injective_immersion_of_scalar_jets {n : ℕ} (M : ComplexManifold n)
    (hjets : ∀ (pts : Finset M.Carrier) (k : ℕ)
      (Pj : M.Carrier → MvPolynomial (Fin n) ℂ),
      ∃ f, IsHolomorphicFn f ∧ ∀ p ∈ pts, JetAgreeFn f p (Pj p) k) :
    ∃ F : M.Carrier → ComplexVector (2 * n + 1),
      IsHolomorphicVecMap F ∧ Function.Injective F ∧ IsImmersionMap F := by
  obtain ⟨f, hsep, himm⟩ := exists_simultaneous_scalar_tuple M hjets
  refine ⟨scalarTupleMap f, scalarTupleMap_holomorphic f, ?_, ?_⟩
  · intro x y hxy
    apply hsep x y
    intro j
    exact congrArg (fun v : ComplexVector (2 * n + 1) => v j) hxy
  · intro x
    obtain ⟨a, hx, hinj⟩ := himm x
    exact scalarTupleMap_intrinsic_derivative_injective f a x hx hinj

end Yau.NodeProofs.P03Aux
