import Yau.Proofs.C01JointDirections

/-! The Jacobian cancels from the determinant quotient of the same two
metrics.  This uses the actual chart frames, not a new curvature or Ricci
naturality input.  The inverse-chart differentiation is the elementary
Mathlib proof also used in canonical L12; the determinant algebra follows
canonical L17ChartNaturality at A e0dbe0df, proved here in our own consumer. -/

noncomputable section

open scoped Manifold Topology ContDiff Matrix ComplexOrder

namespace Yau.NodeProofs.C01Aux

open Yau Yau.Blueprint
open Yau.Blueprint.Alignment.Y03Proof

variable {n : ℕ} {M : ComplexManifold n}

theorem chartVec_tangentCoords (x y : M.Carrier)
    (hy : y ∈ (extChartAt (ComplexModel n) x).source) (v : TangentVector M y) :
    chartVec x y (tangentCoords x y v) = v := by
  have hcomp := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt'
    (I := ComplexModel n) hy
  rw [ModelWithCorners.range_eq_univ, mfderivWithin_univ] at hcomp
  exact congrArg (fun L => L v) hcomp

theorem chartVec_basis_sum (x y : M.Carrier) (v : ComplexVector n) :
    (∑ i, v i • chartVec x y (stdVec i)) = chartVec x y v := by
  have hb : (∑ i, v i • stdVec i) = v := by
    ext i
    simp [stdVec, EuclideanSpace.single, Pi.single_apply]
  calc
    _ = ∑ i, chartVec x y (v i • stdVec i) :=
      Finset.sum_congr rfl fun i _ => (chartVec_smul _ _ _ _).symm
    _ = chartVec x y (∑ i, v i • stdVec i) :=
      (map_sum (mfderiv (ComplexModel n) (ComplexModel n)
        (extChartAt (ComplexModel n) x).symm (chartPt x y)) _ _).symm
    _ = _ := congrArg (chartVec x y) hb

theorem tangentVector_center_frame_expansion (y : M.Carrier) (v : TangentVector M y) :
    v = ∑ i, tangentCoords y y v i • chartVec y y (stdVec i) := by
  rw [chartVec_basis_sum, chartVec_tangentCoords y y (mem_extChartAt_source y)]

def centerFrameMatrix (x y : M.Carrier) : Herm n :=
  fun i j => tangentCoords y y (chartVec x y (stdVec j)) i

theorem hMat_center_congruence (k : HermitianField M) (x : M.Carrier)
    (z : ComplexVector n) :
    hMat k x z = (centerFrameMatrix x (chartInv x z))ᴴ *
      gMat k (chartInv x z) * centerFrameMatrix x (chartInv x z) := by
  let y := chartInv x z
  have hcenter : chartInv y (chartPt y y) = y :=
    (extChartAt (ComplexModel n) y).left_inv (mem_extChartAt_source y)
  let G : Herm n := fun i j => (k y).toFun
    (chartVec y y (stdVec i)) (chartVec y y (stdVec j))
  have hG : gMat k y = G := by
    unfold gMat hMat
    rw [hcenter]
  change hMat k x z = (centerFrameMatrix x y)ᴴ * gMat k y * centerFrameMatrix x y
  rw [hG]
  ext a b
  change (k y).toFun (chartVec x y (stdVec a)) (chartVec x y (stdVec b)) =
    ((centerFrameMatrix x y)ᴴ * G * centerFrameMatrix x y) a b
  calc
    _ = (k y).toFun
        (∑ i, tangentCoords y y (chartVec x y (stdVec a)) i • chartVec y y (stdVec i))
        (∑ j, tangentCoords y y (chartVec x y (stdVec b)) j • chartVec y y (stdVec j)) := by
      rw [← tangentVector_center_frame_expansion, ← tangentVector_center_frame_expansion]
    _ = _ := by
      rw [hermitian_sum_left]
      simp only [hermitian_sum_right, HermitianInnerProduct.map_smul_left,
        HermitianInnerProduct.map_smul_right]
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
      simp only [centerFrameMatrix, G]
      rw [Finset.sum_comm]

theorem frame_congruence_det (H J : Herm n) :
    (Jᴴ * H * J).det = (Complex.normSq J.det : ℂ) * H.det := by
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose]
  calc
    star J.det * H.det * J.det = (star J.det * J.det) * H.det := by ring
    _ = _ := by rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self]

theorem frame_congruence_det_re (H J : Herm n) :
    (Jᴴ * H * J).det.re = Complex.normSq J.det * H.det.re := by
  rw [frame_congruence_det]
  simp

theorem centerFrameMatrix_det_ne_zero (x : M.Carrier) (z : ComplexVector n)
    (hz : z ∈ chartTarget x) (k : HermitianField M) :
    (centerFrameMatrix x (chartInv x z)).det ≠ 0 := by
  intro hzero
  have heq := congrArg Matrix.det (hMat_center_congruence k x z)
  rw [frame_congruence_det, hzero, map_zero, Complex.ofReal_zero, zero_mul] at heq
  exact ((hMat_posDef k x z hz).isUnit.map Matrix.detMonoidHom).ne_zero heq

theorem hMat_determinant_ratio_center (k g : HermitianField M)
    (x : M.Carrier) (z : ComplexVector n) (hz : z ∈ chartTarget x) :
    (hMat k x z).det.re / (hMat g x z).det.re =
      (gMat k (chartInv x z)).det.re / (gMat g (chartInv x z)).det.re := by
  rw [hMat_center_congruence k x z, hMat_center_congruence g x z,
    frame_congruence_det_re, frame_congruence_det_re]
  exact mul_div_mul_left _ _
    (Complex.normSq_pos.mpr (centerFrameMatrix_det_ne_zero x z hz k)).ne'

end Yau.NodeProofs.C01Aux
