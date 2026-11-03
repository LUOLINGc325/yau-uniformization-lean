import Yau.LeafProofs.L19LiYauGaussian
import spec.CHAIN.LeafObligations

/-! Exact original L19, with both complete Li--Yau estimates. -/
namespace Yau.LeafProofs

theorem L19 : Yau.LeafObligations.L19 := by
  exact ⟨L19Aux.liYauDifferential, L19Aux.liYauGaussian⟩

end Yau.LeafProofs
