import Yau.LeafProofs.L10DiscEnergyExact
import Yau.LeafProofs.L10InteriorExact

/-! Both frozen original L10 assertions, with no additional source or hypothesis. -/

namespace Yau.LeafProofs

theorem L10 : LeafObligations.L10 :=
  ⟨discDirichletEstimate, interiorEllipticEstimate⟩

end Yau.LeafProofs
