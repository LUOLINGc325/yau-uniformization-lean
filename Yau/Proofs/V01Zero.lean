import spec.CHAIN.CONTRACTS
import Yau.Proofs.F03PositiveDimension

/-! The original connected noncompact manifold assumptions exclude dimension
zero. Reuse the published proof of this geometric fact. -/

noncomputable section

namespace Yau.Blueprint.V01Proof

theorem envelopeInequality_zero (X : KahlerManifold 0) (h : Flow X) :
    EnvelopeInequality X h :=
  (Yau.Proofs.F03Aux.complexManifold_zero_false X.manifold).elim

end Yau.Blueprint.V01Proof
