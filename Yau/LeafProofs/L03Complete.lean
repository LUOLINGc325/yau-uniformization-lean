import Yau.LeafProofs.L03HodgeAdjointDeficiency
import Yau.LeafProofs.L03PositiveClosure
import Yau.LeafProofs.L03DiracComplete

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

namespace Yau.LeafProofs.L03

variable {n k : ℕ} {M : ComplexManifold n}

/-- The closure of the actual Hodge compact core is its genuine Hilbert
adjoint. The negative deficiency argument uses actual L² section
representatives, local PDE regularization and quantitative cutoffs. -/
theorem hodgeCoreOperator_closure_eq_adjoint
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (k : ℕ) : (hodgeCoreOperator g μ hμ k).closure = (hodgeCoreOperator g μ hμ k).adjoint :=
  positive_closure_eq_adjoint (L2FormHilbert g μ k) (hodgeCoreOperator g μ hμ k)
    (hodgeCoreOperator_domain_dense g μ hμ k) (hodgeCoreOperator_symmetric g μ hμ k)
    (hodgeCoreOperator_nonnegative g μ hμ k) (hodgeCoreOperator_adjoint_neg_self_eq_zero g μ hμ k)

theorem hodgeMaximalGraph_implies_minimal
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (A W : RealForm M k) (hmax : OperatorCandidates.HodgeMaximalGraph g.form μ A W) :
    OperatorCandidates.HodgeMinimalGraph g.form μ A W := by
  apply (hodgeMinimalGraph_iff_operator_closure g μ hμ A W hmax.1 hmax.2.1).mpr
  rw [hodgeCoreOperator_closure_eq_adjoint g μ hμ k]
  exact (hodgeMaximalGraph_iff_operator_adjoint g μ hμ A W hmax.1 hmax.2.1).mp hmax

/-- The exact original Hodge minimal/maximal graph equality. -/
theorem hodgeEssentialSelfAdjointness : OperatorCandidates.HodgeEssentialSelfAdjointness := by
  intro n M g _ _ μ hμ k A W
  exact ⟨hodgeMinimalGraph_implies_maximal g μ hμ, hodgeMaximalGraph_implies_minimal g μ hμ A W⟩

end Yau.LeafProofs.L03

namespace Yau.LeafProofs

/-- L03 with its exact closed quantification: Hodge ESA, full graded
Dirac ESA, and the complex Hilbert inference from the square. -/
theorem L03 : Yau.LeafObligations.L03 :=
  ⟨L03.hodgeEssentialSelfAdjointness, L03.diracEssentialSelfAdjointness,
    L03.essentialSelfAdjointOfSquare_all⟩

end Yau.LeafProofs
