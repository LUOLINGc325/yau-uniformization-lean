import Yau.Proofs.F04CoerciveEvolutionExistence
import Yau.Proofs.F04VariationalUniqueness

open MeasureTheory Filter Set TopologicalSpace
open scoped Topology InnerProductSpace

noncomputable section

namespace Yau.F04Proof

open Yau.MassTargetStatements

/-- The literal original evolution OUTPUT follows from the internally proved
 Galerkin/Riesz construction and original-trace uniqueness. -/
theorem variationalEvolutionOutput_of_constructed_form
    {n : ℕ} {M : ComplexManifold n}
    {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V] [SeparableSpace V]
    (μ : Measure M.Carrier) (O : Set M.Carrier) {T C α shift : ℝ}
    (hT : 0 < T) (hC : 0 ≤ C) (hα : 0 < α) (hshift : 0 ≤ shift)
    (j : V →L[ℝ] FixedPivot μ O) (hj : ‖j‖ ≤ 1) (hjinj : Function.Injective j) (hjd : DenseRange j)
    (B : ℝ → V →L[ℝ] EnergyDual V) (hB : ∀ t, ‖B t‖ ≤ C)
    (hcB : ∀ u v, Continuous (fun t => B t u v))
    (hGard : ∀ t ∈ Icc 0 T, ∀ v : V, α * ‖v‖ ^ 2 ≤ B t v v + shift * ‖j v‖ ^ 2) :
    ∃ E : ℝ, VariationalEvolutionOutput μ O T E j B := by
  obtain ⟨E, hE, hExists⟩ := coercive_variational_evolution_exists hT hC hα hshift j hj hjinj hjd B hB hcB hGard
  refine ⟨E, hE, ?_⟩
  intro f hf
  obtain ⟨u, w, a, hu, hw, ha, ha0, hAE, hScalar, hEq, hEnergy, hTrace⟩ := hExists f hf
  have hSol : VariationalSolution μ O T j B f u w a := ⟨hu, hw, ha, ha0, hAE, hScalar, hEq⟩
  refine ⟨u, w, a, hSol, hEnergy, hTrace, ?_⟩
  intro v z b hSol₂
  exact variationalSolution_unique_of_coercive μ O hT j hj hjinj B α shift hα hshift hGard
    f u v w z a b hSol hSol₂

end Yau.F04Proof
