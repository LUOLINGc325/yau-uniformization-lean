import spec.CHAIN.LeafObligations
import Mathlib.RingTheory.Filtration

namespace Yau.LeafProofs

/-- Krull intersection for every finite module over a Noetherian local ring. -/
theorem L25 : Yau.LeafObligations.L25 := by
  intro R A _ _ _ _ _ _ I hI
  exact Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := A) I hI

end Yau.LeafProofs
