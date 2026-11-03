import Yau.Proofs.P06ScalarUniquenessRicciPositive

noncomputable section
open scoped Matrix ComplexOrder

namespace Yau.Proofs.P04Aux
open Yau
variable {n : ℕ}

/-- The canonical shared proof supplies the exact original initial Ricci
sign, with no additional geometric or analytic premise. -/
theorem initial_ricci_posSemidef (X : KahlerManifold n) (x : Yau.Blueprint.Pt X) :
    (ricci X.metric.form x).PosSemidef :=
  Yau.NodeProofs.P06Aux.kahlerManifold_ricci_posSemidef X x

end Yau.Proofs.P04Aux
