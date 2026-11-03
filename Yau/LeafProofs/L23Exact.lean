import Yau.LeafProofs.L23DistanceSupportComplete
import Yau.LeafProofs.L23CurvatureDerivativeAssembly
import spec.CHAIN.LeafObligations

/-! The frozen local curvature derivative leaf for the original curvature jets. -/

namespace Yau.LeafProofs

theorem L23Exact : Yau.LeafObligations.L23 := by
  apply L23Aux.localCurvatureDerivatives_of_supportConstruction
  intro n M h p a K r τ σ hK hr hτ hσ hO hcO hflow hcurv
  exact L23Aux.derivativeCutoffSupports h p a K r τ σ hK hr hτ hσ hO hcO hflow hcurv

end Yau.LeafProofs
