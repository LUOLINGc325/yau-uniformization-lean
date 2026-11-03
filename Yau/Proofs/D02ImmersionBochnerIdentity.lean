import Yau.Proofs.D02DualBochnerIdentity

/-! The computed Bochner identity for the actual dF component norm. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
open Filter
namespace Yau.NodeProofs.D02Aux
open Yau Yau.Blueprint Yau.LeafProofs.L14Aux Yau.Blueprint.V03Proof
set_option backward.isDefEq.respectTransparency false

variable {n N : ℕ} {M : ComplexManifold n}

def immersionDualCurvatureMatrix (g : HermitianField M) (x : M.Carrier)
    (z v : ComplexVector n) : Matrix (Fin n) (Fin n) ℂ :=
  -directionMatrixWirtBar (fun w => directionMatrixWirt (fun u => (hMat g x u)ᵀ) w v) z v +
    directionMatrixWirt (fun u => (hMat g x u)ᵀ) z v * ((hMat g x z)ᵀ)⁻¹ *
      directionMatrixWirtBar (fun u => (hMat g x u)ᵀ) z v

theorem immersionComponent_dualBochner (g : HermitianField M) (hg : MetricSmooth g)
    {F : M.Carrier → ComplexVector N} (hF : IsHolomorphicVecMap F) (x : M.Carrier)
    (a : Fin N) {z : ComplexVector n} (hz : z ∈ chartTarget x) (v : ComplexVector n) :
    wirtBar (fun w => wirt (fun u => (dualNormMat (hMat g x u)
      (WithLp.toLp 2 (fun b => immersionDerivativeMatrix F x u a b)) : ℂ)) w v) z v =
      star (vectorWirt (raisedImmersionComponent g F x a) z v) ⬝ᵥ (hMat g x z)ᵀ *ᵥ
        vectorWirt (raisedImmersionComponent g F x a) z v +
      star (raisedImmersionComponent g F x a z) ⬝ᵥ immersionDualCurvatureMatrix g x z v *ᵥ
        raisedImmersionComponent g F x a z := by
  let D := fun w => (hMat g x w)ᵀ
  let η := fun w b => immersionDerivativeMatrix F x w a b
  let t := raisedImmersionComponent g F x a
  let q := fun w => (dualNormMat (hMat g x w) (WithLp.toLp 2 (η w)) : ℂ)
  have hU : IsOpen (chartTarget x) := isOpen_extChartAt_target (I := ComplexModel n) x
  have he : (fun w => wirt q w v) =ᶠ[𝓝 z]
      (fun w => wirt (fun u => star (η u) ⬝ᵥ t u) w v) := by
    filter_upwards [hU.mem_nhds hz] with w hw
    have hNear : q =ᶠ[𝓝 w] (fun u => star (η u) ⬝ᵥ t u) := by
      filter_upwards [hU.mem_nhds hw] with u hu
      exact dualNormMat_coe_eq_raisedPairing (hMat_posDef g x u hu) _
    unfold wirt
    rw [hNear.fderiv_eq]
  have hEq : wirtBar (fun w => wirt q w v) z v =
      wirtBar (fun w => wirt (fun u => star (η u) ⬝ᵥ t u) w v) z v := by
    unfold wirtBar
    rw [he.fderiv_eq]
  change wirtBar (fun w => wirt q w v) z v = _
  rw [hEq]
  exact dualBochner_identity hU D t η
    (fun b c => Yau.LeafProofs.L17Aux.hMat_contDiffOn_of_metricSmooth g hg x c b)
    (raisedImmersionComponent_contDiffOn g hg hF x a)
    (immersionDerivativeMatrix_differentiableOn hF x a)
    (fun w hw => (hMat_posDef g x w hw).transpose)
    (fun w hw => raisedImmersionComponent_lowering g F x a hw) z v hz

end Yau.NodeProofs.D02Aux
