import Yau.Proofs.C03ChernGaugeFlat
import Yau.Proofs.E01ChernContraction
import Yau.Proofs.E01MatrixWirtAdjoint

/-! The literal dual inverse-transpose residual is the actual source Chern
bisectional contraction on the conjugated raised vector. -/

noncomputable section
open scoped Topology ContDiff Manifold Matrix

namespace Yau.Proofs.C03Aux.ChernGauge

open Yau Yau.Blueprint Yau.LeafProofs L12Aux Yau.NodeProofs.E01Aux
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

def computedResidual (H : ComplexVector n → Herm n) (z ξ a : ComplexVector n) : ℝ :=
  ellipsoidQuadratic
    ((H z)⁻¹ᵀ * ((complexMatrixWirt H z a)ᵀ * (H z)⁻¹ᵀ *
      ((complexMatrixWirt H z a)ᴴ)ᵀ -
        (complexMatrixWirt (fun w => complexMatrixWirtBar H w a) z a)ᵀ) * (H z)⁻¹ᵀ) ξ

theorem source_residual_eq_bisectional
    (hn : 1 ≤ n) (k : HermitianField (ComplexEuclideanManifold n hn)) (ks : MetricSmooth k)
    (z : (ComplexEuclideanManifold n hn).Carrier) (ξ a : ComplexVector n) :
    computedResidual (fun w => gMat k w) z ξ a =
      bisectionalForm k z
        (WithLp.toLp 2 (star (WithLp.ofLp (matrixFiberMap (gMat k z)⁻¹ᵀ ξ)))) a := by
  let H : ComplexVector n → Herm n := fun w => gMat k w
  let K : Herm n := (gMat k z)⁻¹ᵀ
  have hflat : hMat k z = H := by
    funext w
    exact flat_hMat_eq_gMat hn k z w
  have hHerm : ∀ w, (H w).IsHermitian := by
    intro w
    rw [← hflat]
    exact L12Aux.hMat_isHermitian k z w
  have hK : K.IsHermitian := (hHerm z).inv.transpose
  let A := complexMatrixWirt H z a
  let B := complexMatrixWirt (fun w => complexMatrixWirtBar H w a) z a
  let R := Aᵀ * K * (Aᴴ)ᵀ - Bᵀ
  have hc : ellipsoidQuadratic R (matrixFiberMap K ξ) =
      bisectionalForm k z
        (WithLp.toLp 2 (star (WithLp.ofLp (matrixFiberMap K ξ)))) a := by
    have HC := centered_chern_residual_contraction k ks z (matrixFiberMap K ξ) a
    rw [hflat, flat_chartPt hn, complexMatrixWirtBar_of_hermitian H hHerm] at HC
    exact HC
  change ellipsoidQuadratic (K * R * K) ξ = _
  calc
    _ = ellipsoidQuadratic R (matrixFiberMap K ξ) := by
      rw [ellipsoidQuadratic_matrixFiberMap, hK.eq]
    _ = _ := hc

end Yau.Proofs.C03Aux.ChernGauge
