import Yau.LeafProofs.L05AutonomousSchauder
import Yau.LeafProofs.L05PerturbationSchauder
import Yau.LeafProofs.L05ChuFromCoarse

namespace Yau.LeafProofs

/-- The original three-component Chu leaf, with every analytic dependency proved internally. -/
theorem L05 : Yau.LeafObligations.L05 :=
  L05Aux.leaf_L05_of_coarse
    (L05Aux.variable_concave_coarse_schauder_of_autonomous
      L05Aux.autonomous_concave_schauder)

end Yau.LeafProofs
