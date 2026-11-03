import Yau.LeafProofs.L19BochnerIdentityCD
import Yau.LeafProofs.L19Localization

/-! The complete original Li--Yau differential estimate. -/

noncomputable section

open scoped ComplexOrder

namespace Yau.LeafProofs.L19Aux

variable {n : ℕ} {M : ComplexManifold n}

/-- The actual Bochner computation supplies the precise hypothesis used
by the compact-cylinder localization proof. -/
theorem complexCD (g : SmoothMetric M) (hK : IsKahler g)
    (hRic : ∀ x, (ricci g.form x).PosSemidef) : ComplexCD g := by
  intro f hf x
  exact complexCD_inequality g hK hRic hf x

/-- The frozen original differential statement, for every positive heat
solution, with all geometric and localization bridges proved internally. -/
theorem liYauDifferential : LeafCandidates.LiYauDifferential := by
  intro n M g _ hK hRic u hu x t ht
  exact liYau_at_point_of_CD g (L12Aux.complexDimension_pos M) hK hRic
    (complexCD g hK hRic) hu x ht

end Yau.LeafProofs.L19Aux
