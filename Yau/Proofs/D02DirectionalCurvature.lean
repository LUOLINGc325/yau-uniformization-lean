import Yau.Proofs.D02WirtingerDirections
import Yau.Proofs.G01ChernCurvature

/-! The Bochner curvature matrix is exactly the contraction of the original
Chern calculator, in its original fixed chart and index order. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
namespace Yau.NodeProofs.D02Aux
open Yau Yau.Blueprint.V03Proof Yau.LeafProofs.L14Aux
set_option backward.isDefEq.respectTransparency false

def dualCurvatureBilinearMatrix {n r : ℕ}
    (D : ComplexVector n → Matrix (Fin r) (Fin r) ℂ)
    (z : ComplexVector n) (p q : Fin n) : Matrix (Fin r) (Fin r) ℂ :=
  -directionMatrixWirtBar (fun w => directionMatrixWirt D w (stdVec p)) z (stdVec q) +
    directionMatrixWirt D z (stdVec p) * (D z)⁻¹ * directionMatrixWirtBar D z (stdVec q)

theorem immersionDualCurvatureMatrix_expansion {n : ℕ} {M : ComplexManifold n}
    (g : HermitianField M) (hg : MetricSmooth g) (x : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget x) (v : ComplexVector n) :
    immersionDualCurvatureMatrix g x z v = ∑ p, ∑ q, (v p * star (v q)) •
      dualCurvatureBilinearMatrix (fun w => (hMat g x w)ᵀ) z p q := by
  unfold immersionDualCurvatureMatrix
  rw [mixedMatrixWirt_coordinates
    (isOpen_extChartAt_target (I := ComplexModel n) x) (fun w => (hMat g x w)ᵀ)
    (fun a b => Yau.LeafProofs.L17Aux.hMat_contDiffOn_of_metricSmooth g hg x b a) z v hz,
    directionMatrixWirt_coordinates (fun w => (hMat g x w)ᵀ) z v,
    directionMatrixWirtBar_coordinates (fun w => (hMat g x w)ᵀ) z v]
  simp only [dualCurvatureBilinearMatrix, Matrix.sum_mul, Matrix.mul_sum,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, Finset.sum_neg_distrib,
    Finset.sum_add_distrib, smul_add, smul_neg, Finset.smul_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  rw [mul_comm (star (v q)) (v p)]

theorem dualCurvatureBilinearMatrix_hMat {n : ℕ} {M : ComplexManifold n}
    (g : HermitianField M) (hg : MetricSmooth g) (x : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget x) (p q a b : Fin n) :
    dualCurvatureBilinearMatrix (fun w => (hMat g x w)ᵀ) z p q a b =
      G01Aux.chernInChart g x z a b p q := by
  have hf : ContDiffAt ℝ 2 (fun w => hMat g x w b a) z :=
    ((Yau.LeafProofs.L17Aux.hMat_contDiffOn_of_metricSmooth g hg x b a).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).of_le (by simp)
  have hc := wirt_wirtBar_comm (fun w => hMat g x w b a) z hf (stdVec q) (stdVec p)
  simp only [dualCurvatureBilinearMatrix, directionMatrixWirtBar, directionMatrixWirt,
    Matrix.add_apply, Matrix.neg_apply, ← Matrix.transpose_nonsing_inv, Matrix.transpose_apply,
    Matrix.mul_apply, G01Aux.chernInChart]
  rw [← hc]
  congr 1
  apply Finset.sum_congr rfl
  intro c _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d _
  ring

theorem immersionDualCurvatureMatrix_center {n : ℕ} {M : ComplexManifold n}
    (g : HermitianField M) (hg : MetricSmooth g) (x : M.Carrier) (v : ComplexVector n)
    (a b : Fin n) :
    immersionDualCurvatureMatrix g x (chartPt x x) v a b =
      ∑ p, ∑ q, (v p * star (v q)) * chernCurvature g x a b p q := by
  have he := congrArg (fun A : Matrix (Fin n) (Fin n) ℂ => A a b)
    (immersionDualCurvatureMatrix_expansion g hg x (z := chartPt x x) (mem_extChartAt_target x) v)
  rw [he]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  rw [dualCurvatureBilinearMatrix_hMat g hg x (z := chartPt x x) (mem_extChartAt_target x) p q a b]
  rfl

theorem immersionDualCurvatureMatrix_center_pairing {n : ℕ} {M : ComplexManifold n}
    (g : HermitianField M) (hg : MetricSmooth g) (x : M.Carrier) (v : ComplexVector n)
    (t : Fin n → ℂ) :
    (star t ⬝ᵥ immersionDualCurvatureMatrix g x (chartPt x x) v *ᵥ t).re =
      bisectionalForm g x (WithLp.toLp 2 (star t)) v := by
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, immersionDualCurvatureMatrix_center g hg x v,
    Finset.mul_sum, Finset.sum_mul]
  unfold bisectionalForm
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  simp only [WithLp.ofLp_toLp, Pi.star_apply, star_star]
  ring

end Yau.NodeProofs.D02Aux
