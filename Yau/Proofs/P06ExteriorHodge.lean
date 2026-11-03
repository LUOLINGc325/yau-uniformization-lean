import Yau.Proofs.P06Geometry
import Yau.Proofs.P06FormDomain

noncomputable section
open MeasureTheory

namespace Yau.NodeProofs.P06Aux
open Yau Yau.LeafProofs.L03
variable {n k : ℕ} {M : ComplexManifold n}

/-- The actual reconstructed exterior derivative squares to zero. -/
theorem exterior_square_zero (A : RealForm M k) (hA : SmoothRealForm A) :
    exteriorRealForm (exteriorRealForm A) = 0 :=
  G04Aux.exterior_closed_eq_zero (exteriorRealForm A)
    (exteriorRealForm_smooth A hA) (exteriorRealForm_closed A hA)

/-- Exterior differentiation commutes with the actual Hodge expression in
all degrees. This identity does not require type or curvature assumptions. -/
theorem exterior_hodge_commute (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A : RealForm M k) (hA : SmoothRealForm A) :
    exteriorRealForm (hodgeRealForm g.form k A) =
      hodgeRealForm g.form (k + 1) (exteriorRealForm A) := by
  cases k with
  | zero =>
    simp only [hodgeRealForm]
    rw [exterior_square_zero A hA, codifferentialRealForm_zero g μ hμ 1, add_zero]
  | succ k =>
    have hdδA := exteriorRealForm_smooth (codifferentialRealForm g.form A)
      (codifferentialRealForm_smooth g μ hμ A hA)
    have hδdA := codifferentialRealForm_smooth g μ hμ (exteriorRealForm A)
      (exteriorRealForm_smooth A hA)
    simp only [hodgeRealForm]
    rw [exteriorRealForm_add _ _ hdδA hδdA,
      exterior_square_zero (codifferentialRealForm g.form A)
        (codifferentialRealForm_smooth g μ hμ A hA),
      zero_add, exterior_square_zero A hA, codifferentialRealForm_zero g μ hμ (k + 2), add_zero]

end Yau.NodeProofs.P06Aux
