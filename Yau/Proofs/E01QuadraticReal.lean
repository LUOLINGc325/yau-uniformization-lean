import Yau.Proofs.E01Matrix
import Mathlib.Analysis.Matrix.Hermitian

/-! For Hermitian matrices the original real quadratic calculator equals the genuine complex pairing. -/

noncomputable section
open scoped Matrix

namespace Yau.NodeProofs.E01Aux
open Yau Yau.Blueprint

variable {n : ℕ}

theorem ellipsoidQuadratic_complex_eq (K : Herm n) (hK : K.IsHermitian) (ξ : ComplexVector n) :
    (ellipsoidQuadratic K ξ : ℂ) = star (WithLp.ofLp ξ) ⬝ᵥ (K *ᵥ WithLp.ofLp ξ) := by
  apply Complex.ext
  · rfl
  · simpa only [Complex.ofReal_im, RCLike.im_eq_complex_im] using (hK.im_star_dotProduct_mulVec_self (WithLp.ofLp ξ)).symm

theorem dualNormMat_complex_eq (H : Herm n) (hH : H.IsHermitian) (ξ : ComplexVector n) :
    (dualNormMat H ξ : ℂ) = star (WithLp.ofLp ξ) ⬝ᵥ ((H⁻¹)ᵀ *ᵥ WithLp.ofLp ξ) :=
  ellipsoidQuadratic_complex_eq (H⁻¹)ᵀ hH.inv.transpose ξ

end Yau.NodeProofs.E01Aux
