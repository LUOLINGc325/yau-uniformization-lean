import Yau.Proofs.V01EmbeddingImmersion
import Yau.Proofs.V01HamiltonianFields

/-! V01 scratch source: the cotangent geometric inlet is constructed from
the exact original P03 conclusion, for the actual given manifold. -/

noncomputable section

namespace Yau.Blueprint.V01Proof

theorem cotangent_setup_of_finiteInterpolation
    {n : ℕ} (X : KahlerManifold n) (hP03 : FiniteInterpolation X) :
    ∃ (q : ℕ) (G : CotangentPoint X.manifold → ComplexVector q),
      CotangentImmersion G ∧ CotangentSpanningFields X.manifold := by
  obtain ⟨q, G, hG⟩ := exists_cotangentImmersion_of_finiteInterpolation hP03
  exact ⟨q, G, hG, cotangentSpanningFields_of_immersion hG⟩

end Yau.Blueprint.V01Proof
