import Yau.Proofs.G01ChernCalculus

noncomputable section
open Filter
open scoped Manifold Topology ContDiff Matrix ComplexOrder
namespace Yau.NodeProofs.G01Aux
open Yau Yau.LeafProofs
variable {n : ℕ} {M : ComplexManifold n}

/-- The computed Chern connection has no pure holomorphic curvature. -/
theorem chernA_holomorphic_flat (h : HermitianField M) (hs : MetricSmooth h)
    (x : M.Carrier) (z : ComplexVector n) (hz : z ∈ chartTarget x) (k l : Fin n) :
    matrixWirt (fun w => chernA h x w l) z k -
      matrixWirt (fun w => chernA h x w k) z l +
      chernA h x z k * chernA h x z l - chernA h x z l * chernA h x z k = 0 := by
  have hH (a b : Fin n) : DifferentiableAt ℝ (fun w => hMat h x w a b) z :=
    ((L17Aux.hMat_contDiffOn_of_metricSmooth h hs x a b).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).differentiableAt (by simp)
  have hA (i a b : Fin n) : DifferentiableAt ℝ (fun w => chernA h x w i a b) z :=
    ((chernA_contDiffOn h hs x i a b).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).differentiableAt (by simp)
  have hd (p q : Fin n) :
      matrixWirt (fun w => hMat h x w * chernA h x w q) z p =
        matrixWirt (fun w => matrixWirt (hMat h x) w q) z p := by
    ext a b
    have he : (fun w => (hMat h x w * chernA h x w q) a b) =ᶠ[𝓝 z]
        (fun w => matrixWirt (hMat h x) w q a b) := by
      filter_upwards [(isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz] with w hw
      exact congrArg (fun A => A a b) (chernA_lower h x w hw q)
    unfold matrixWirt wirt
    rw [he.fderiv_eq]
    rfl
  have hc : matrixWirt (fun w => matrixWirt (hMat h x) w l) z k =
      matrixWirt (fun w => matrixWirt (hMat h x) w k) z l := by
    ext a b
    have hf : ContDiffAt ℝ 2 (fun w => hMat h x w a b) z :=
      ((L17Aux.hMat_contDiffOn_of_metricSmooth h hs x a b).contDiffAt
        ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).of_le (by simp)
    exact wirt_wirt_comm _ z hf (stdVec l) (stdVec k)
  have he := (hd k l).trans (hc.trans (hd l k).symm)
  rw [matrixWirt_mul _ _ z hH (hA l) k,
    matrixWirt_mul _ _ z hH (hA k) l,
    ← chernA_lower h x z hz k, ← chernA_lower h x z hz l] at he
  have hz0 : hMat h x z *
      (matrixWirt (fun w => chernA h x w l) z k -
        matrixWirt (fun w => chernA h x w k) z l +
        chernA h x z k * chernA h x z l - chernA h x z l * chernA h x z k) = 0 := by
    calc
      _ = (hMat h x z * chernA h x z k * chernA h x z l +
          hMat h x z * matrixWirt (fun w => chernA h x w l) z k) -
        (hMat h x z * chernA h x z l * chernA h x z k +
          hMat h x z * matrixWirt (fun w => chernA h x w k) z l) := by noncomm_ring
      _ = 0 := sub_eq_zero.mpr he
  have hi := congrArg (fun A => (hMat h x z)⁻¹ * A) hz0
  rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _
    ((L12Aux.hMat_posDef h x z hz).isUnit.map Matrix.detMonoidHom),
    Matrix.one_mul, Matrix.mul_zero] at hi
  exact hi

end Yau.NodeProofs.G01Aux
