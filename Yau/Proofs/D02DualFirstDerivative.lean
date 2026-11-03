import Yau.Proofs.D02DualLowering

/-! The first derivative in the dual Bochner calculation, for the actual
inverse-transpose raised immersion covector. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
open Filter
namespace Yau.NodeProofs.D02Aux
open Yau Yau.Blueprint Yau.Blueprint.V03Proof Yau.LeafProofs.L14Aux

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {r : ℕ}

theorem wirt_dual_pairing_lowered (D : V → Matrix (Fin r) (Fin r) ℂ)
    (η t : V → Fin r → ℂ) (z v : V) (hD : (D z).IsHermitian)
    (hLower : D z *ᵥ t z = η z)
    (hη : ∀ a, DifferentiableAt ℂ (fun w => η w a) z)
    (ht : ∀ a, DifferentiableAt ℝ (fun w => t w a) z) :
    wirt (fun w => star (η w) ⬝ᵥ t w) z v =
      star (t z) ⬝ᵥ D z *ᵥ vectorWirt t z v := by
  rw [wirt_holomorphic_pairing η t z v hη ht, ← hLower, Matrix.star_mulVec, hD.eq,
    ← Matrix.dotProduct_mulVec]

variable {n N : ℕ} {M : ComplexManifold n}

theorem dualNormMat_coe_eq_raisedPairing {H : Matrix (Fin n) (Fin n) ℂ}
    (hH : H.PosDef) (η : Fin n → ℂ) :
    (dualNormMat H (WithLp.toLp 2 η) : ℂ) = star η ⬝ᵥ raisedCovector H η := by
  have him := hH.inv.transpose.isHermitian.im_star_dotProduct_mulVec_self η
  apply Complex.ext
  · rfl
  · change (0 : ℝ) = (star η ⬝ᵥ H⁻¹ᵀ *ᵥ η).im
    exact him.symm

theorem immersionComponent_dualNorm_wirt (g : HermitianField M) (hg : MetricSmooth g)
    {F : M.Carrier → ComplexVector N} (hF : IsHolomorphicVecMap F) (x : M.Carrier)
    (a : Fin N) {z : ComplexVector n} (hz : z ∈ chartTarget x) (v : ComplexVector n) :
    wirt (fun w => (dualNormMat (hMat g x w)
      (WithLp.toLp 2 (fun b => immersionDerivativeMatrix F x w a b)) : ℂ)) z v =
      star (raisedImmersionComponent g F x a z) ⬝ᵥ (hMat g x z)ᵀ *ᵥ
        vectorWirt (raisedImmersionComponent g F x a) z v := by
  have hU : IsOpen (chartTarget x) := isOpen_extChartAt_target (I := ComplexModel n) x
  have he : (fun w => (dualNormMat (hMat g x w)
      (WithLp.toLp 2 (fun b => immersionDerivativeMatrix F x w a b)) : ℂ)) =ᶠ[𝓝 z]
      (fun w => star (fun b => immersionDerivativeMatrix F x w a b) ⬝ᵥ
        raisedImmersionComponent g F x a w) := by
    filter_upwards [hU.mem_nhds hz] with w hw
    exact dualNormMat_coe_eq_raisedPairing (hMat_posDef g x w hw) _
  have hEq : wirt (fun w => (dualNormMat (hMat g x w)
      (WithLp.toLp 2 (fun b => immersionDerivativeMatrix F x w a b)) : ℂ)) z v =
      wirt (fun w => star (fun b => immersionDerivativeMatrix F x w a b) ⬝ᵥ
        raisedImmersionComponent g F x a w) z v := by
    unfold wirt
    rw [he.fderiv_eq]
  rw [hEq]
  apply wirt_dual_pairing_lowered (fun w => (hMat g x w)ᵀ)
    (fun w b => immersionDerivativeMatrix F x w a b) (raisedImmersionComponent g F x a) z v
    (hMat_posDef g x z hz).transpose.isHermitian (raisedImmersionComponent_lowering g F x a hz)
  · intro b
    exact (immersionDerivativeMatrix_differentiableOn hF x a b z hz).differentiableAt (hU.mem_nhds hz)
  · intro b
    exact ((raisedImmersionComponent_contDiffOn g hg hF x a b).contDiffAt
      (hU.mem_nhds hz)).differentiableAt (by simp)

end Yau.NodeProofs.D02Aux
