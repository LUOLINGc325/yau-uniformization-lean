import Yau.Proofs.E01Congruence

/-! The exact Hermitian square completion used by the dual Chern calculation. -/

noncomputable section
open scoped Matrix ComplexOrder

namespace Yau.NodeProofs.E01Aux
open Yau Yau.Blueprint

variable {n : ℕ}

theorem hermitian_pairing_re_comm (K : Herm n) (hK : K.IsHermitian)
    (u v : ComplexVector n) :
    (star (WithLp.ofLp u) ⬝ᵥ (K *ᵥ WithLp.ofLp v)).re =
      (star (WithLp.ofLp v) ⬝ᵥ (K *ᵥ WithLp.ofLp u)).re := by
  simpa only [Complex.star_def, Complex.conj_re] using
    congrArg Complex.re (hK.star_dotProduct_mulVec_comm (WithLp.ofLp u) (WithLp.ofLp v))

theorem ellipsoidQuadratic_vector_sub (K : Herm n) (hK : K.IsHermitian)
    (u v : ComplexVector n) :
    ellipsoidQuadratic K (u - v) = ellipsoidQuadratic K u + ellipsoidQuadratic K v -
      2 * (star (WithLp.ofLp u) ⬝ᵥ (K *ᵥ WithLp.ofLp v)).re := by
  have hvu := hermitian_pairing_re_comm K hK v u
  change (star (WithLp.ofLp u - WithLp.ofLp v) ⬝ᵥ
    (K *ᵥ (WithLp.ofLp u - WithLp.ofLp v))).re = _
  rw [star_sub, Matrix.mulVec_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub]
  simp only [Complex.sub_re]
  unfold ellipsoidQuadratic
  rw [hvu]
  ring

theorem dual_levi_square_completion (K C R : Herm n) (hK : K.IsHermitian)
    (u ξ : ComplexVector n) :
    ellipsoidQuadratic K u -
        2 * (star (WithLp.ofLp u) ⬝ᵥ (K *ᵥ WithLp.ofLp (matrixFiberMap C ξ))).re +
        ellipsoidQuadratic (Cᴴ * K * C + R) ξ =
      ellipsoidQuadratic K (u - matrixFiberMap C ξ) + ellipsoidQuadratic R ξ := by
  rw [ellipsoidQuadratic_vector_sub K hK,
    ellipsoidQuadratic_matrixFiberMap, ellipsoidQuadratic_add]
  ring

end Yau.NodeProofs.E01Aux
