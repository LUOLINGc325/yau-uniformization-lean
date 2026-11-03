import Yau.Proofs.F03ScalarL2

/-! A native closed-graph transport for the later actual finite jet maps. -/
noncomputable section
open Set
namespace Yau.Proofs.F03Aux

/-- A separating family of genuine continuous scalar tests certifies the
closed graph of an algebraic linear map, when each tested value has an
actual bounded expression on its source. -/
theorem linearMap_isClosed_graph_of_tests
    {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : E →ₗ[ℝ] F) (A : ι → F →L[ℝ] ℝ) (B : ι → E →L[ℝ] ℝ)
    (hsep : ∀ v : F, (∀ i, A i v = 0) → v = 0)
    (hAB : ∀ i x, A i (T x) = B i x) : IsClosed (T.graph : Set (E × F)) := by
  have hgraph : (T.graph : Set (E × F)) = ⋂ i, {p | A i p.2 = B i p.1} := by
    ext p
    constructor
    · intro hp
      change p.2 = T p.1 at hp
      apply Set.mem_iInter.mpr
      intro i
      change A i p.2 = B i p.1
      rw [hp,hAB]
    · intro hp
      change p.2 = T p.1
      apply Eq.symm
      apply sub_eq_zero.mp
      apply hsep
      intro i
      rw [map_sub,hAB]
      have hi := Set.mem_iInter.mp hp i
      exact sub_eq_zero.mpr hi.symm
  rw [hgraph]
  apply isClosed_iInter
  intro i
  exact isClosed_eq ((A i).continuous.comp continuous_snd) ((B i).continuous.comp continuous_fst)

/-- Quantitative boundedness follows from the ordinary Banach closed graph
theorem; no bounded-evaluation premise is smuggled into the argument. -/
theorem linearMap_continuous_of_tests
    {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (T : E →ₗ[ℝ] F) (A : ι → F →L[ℝ] ℝ) (B : ι → E →L[ℝ] ℝ)
    (hsep : ∀ v : F, (∀ i, A i v = 0) → v = 0)
    (hAB : ∀ i x, A i (T x) = B i x) : Continuous T :=
  T.continuous_of_isClosed_graph (linearMap_isClosed_graph_of_tests T A B hsep hAB)

end Yau.Proofs.F03Aux
