import Yau.Proofs.E01MatrixTopology
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Compactness of the actual PSD quadratic minorants. -/

noncomputable section
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Yau.NodeProofs.E01Aux
open Yau Yau.Blueprint

variable {n : ℕ}

theorem ellipsoidQuadratic_sub (A B : Herm n) (η : ComplexVector n) :
    ellipsoidQuadratic (A - B) η = ellipsoidQuadratic A η - ellipsoidQuadratic B η := by
  simp [ellipsoidQuadratic, Matrix.sub_mulVec, dotProduct_sub]

theorem isCompact_psd_order_interval (C : Herm n) :
    IsCompact {A : Herm n | A.PosSemidef ∧ (C - A).PosSemidef} := by
  have hclosed : IsClosed {A : Herm n | A.PosSemidef ∧ (C - A).PosSemidef} :=
    isClosed_posSemidef_matrices.inter
      (isClosed_posSemidef_matrices.preimage (continuous_const.sub continuous_id))
  have hbounded : Bornology.IsBounded
      {A : Herm n | A.PosSemidef ∧ (C - A).PosSemidef} :=
    isBounded_iff_forall_norm_le.mpr ⟨‖C‖, fun A hA =>
      CStarAlgebra.norm_le_norm_of_le_of_nonneg hA.2 hA.1.nonneg⟩
  exact Metric.isCompact_of_isClosed_isBounded hclosed hbounded

theorem psd_minorant_le_upper
    (v : ComplexVector n → EReal) (C : Herm n) (hC : C.IsHermitian)
    (hv : ∀ η, v η ≤ (ellipsoidQuadratic C η : EReal))
    {A : Herm n} (hA : A.PosSemidef)
    (hAv : ∀ η, (ellipsoidQuadratic A η : EReal) ≤ v η) :
    (C - A).PosSemidef := by
  apply (posSemidef_iff_ellipsoidQuadratic_nonneg _).mpr
  refine ⟨hC.sub hA.isHermitian, fun η => ?_⟩
  rw [ellipsoidQuadratic_sub]
  exact sub_nonneg.mpr (EReal.coe_le_coe_iff.mp ((hAv η).trans (hv η)))

theorem isCompact_psd_minorants_of_upper
    (v : ComplexVector n → EReal) (C : Herm n) (hC : C.IsHermitian)
    (hv : ∀ η, v η ≤ (ellipsoidQuadratic C η : EReal)) :
    IsCompact {A : Herm n | A.PosSemidef ∧ ∀ η,
      (ellipsoidQuadratic A η : EReal) ≤ v η} := by
  apply (isCompact_psd_order_interval C).of_isClosed_subset (isClosed_psd_minorants v)
  intro A hA
  exact ⟨hA.1, psd_minorant_le_upper v C hC hv hA.1 hA.2⟩

end Yau.NodeProofs.E01Aux
