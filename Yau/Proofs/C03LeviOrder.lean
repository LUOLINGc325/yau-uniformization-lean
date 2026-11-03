import Yau.Proofs.C03LeviLower
import Yau.Proofs.E01FeasibleCompact

/-! Scalar inequalities for the actual Levi quadratic reassemble to the
original Hermitian matrix order. -/

noncomputable section
open scoped Topology ContDiff Matrix ComplexOrder

namespace Yau.Proofs.C03Aux
open Yau Yau.Blueprint Yau.LeafProofs.L22Aux Yau.NodeProofs.E01Aux

variable {n : ℕ}

theorem HermLE_leviC_of_quadratic (f : ComplexVector n → ℝ) (z : ComplexVector n)
    (hf : ContDiffAt ℝ 2 f z) (H : Herm n) (hH : H.IsHermitian)
    (hlower : ∀ v, ellipsoidQuadratic H v ≤ complexLeviQuadratic f z v) :
    HermLE H (leviC f z) := by
  apply (posSemidef_iff_ellipsoidQuadratic_nonneg _).mpr
  refine ⟨(leviC_isHermitian hf).sub hH, ?_⟩
  intro v
  rw [ellipsoidQuadratic_sub,
    show ellipsoidQuadratic (leviC f z) v = complexLeviQuadratic f z v from
      leviC_quadratic_re hf v]
  exact sub_nonneg.mpr (hlower v)

end Yau.Proofs.C03Aux
