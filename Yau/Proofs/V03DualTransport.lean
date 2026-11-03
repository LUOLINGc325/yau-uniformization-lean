import Yau.Proofs.V03DualTransportAlgebra
import Yau.Proofs.V03Transitions

/-! The actual dual norm is invariant under changes of valid base charts.
All matrices and covectors are the native chart derivatives and coordinates. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

variable {n : ℕ} {M : ComplexManifold n}

def tangentFrameMatrix (x x' y : M.Carrier) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => (tangentCoordChange (ComplexModel n) x x' y (stdVec j)) i

theorem complexVector_basis_sum (v : ComplexVector n) : (∑ i, v i • stdVec i) = v := by
  ext i
  simp [stdVec, EuclideanSpace.single, Pi.single_apply]

theorem tangentFrameMatrix_mulVec (x x' y : M.Carrier) (v : ComplexVector n) :
    tangentFrameMatrix x x' y *ᵥ WithLp.ofLp v =
      WithLp.ofLp (tangentCoordChange (ComplexModel n) x x' y v) := by
  have hv : tangentCoordChange (ComplexModel n) x x' y v =
      ∑ i, v i • tangentCoordChange (ComplexModel n) x x' y (stdVec i) := by
    conv_lhs => rw [← complexVector_basis_sum v, map_sum]
    simp only [map_smul]
  ext i
  rw [hv]
  simp [tangentFrameMatrix, Matrix.mulVec, dotProduct, mul_comm]

theorem chartVec_eq_centered_sum (x y : M.Carrier)
    (hy : y ∈ (extChartAt (ComplexModel n) x).source) (v : ComplexVector n) :
    chartVec x y v = ∑ i, (tangentCoordChange (ComplexModel n) x y y v) i •
      chartVec y y (stdVec i) := by
  rw [← chartVec_transition y x y (mem_extChartAt_source _) hy]
  conv_lhs => rw [← complexVector_basis_sum
    (tangentCoordChange (ComplexModel n) x y y v), chartVec_sum]
  simp only [chartVec_smul]

theorem tangentFrameMatrix_isUnit (x y : M.Carrier)
    (hy : y ∈ (extChartAt (ComplexModel n) x).source) : IsUnit (tangentFrameMatrix x y y) := by
  have hi : Function.Injective (tangentCoordChange (ComplexModel n) x y y) := by
    intro u v huv
    have hh := congrArg (tangentCoordChange (ComplexModel n) y x y) huv
    simpa only [tangentCoordChange_comp ⟨⟨hy, mem_extChartAt_source _⟩, hy⟩,
      tangentCoordChange_self hy] using hh
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro u v huv
  have hh : WithLp.ofLp (tangentCoordChange (ComplexModel n) x y y (WithLp.toLp 2 u)) =
      WithLp.ofLp (tangentCoordChange (ComplexModel n) x y y (WithLp.toLp 2 v)) := by
    rw [← tangentFrameMatrix_mulVec, ← tangentFrameMatrix_mulVec]
    exact huv
  have hv := hi (congrArg (WithLp.toLp 2) hh)
  exact congrArg WithLp.ofLp hv

set_option backward.isDefEq.respectTransparency false in
theorem hMat_eq_centered_congruence (h : HermitianField M) (x y : M.Carrier)
    (hy : y ∈ (extChartAt (ComplexModel n) x).source) :
    hMat h x (chartPt x y) =
      (tangentFrameMatrix x y y)ᴴ * gMat h y * tangentFrameMatrix x y y := by
  have hround : chartInv x (chartPt x y) = y := (extChartAt (ComplexModel n) x).left_inv hy
  have hself : chartInv y (chartPt y y) = y :=
    (extChartAt (ComplexModel n) y).left_inv (mem_extChartAt_source _)
  have hxentry (a b : Fin n) : hMat h x (chartPt x y) a b =
      (h y).toFun (chartVec x y (stdVec a)) (chartVec x y (stdVec b)) :=
    congrArg (fun z : M.Carrier =>
      (h z).toFun (chartVec x z (stdVec a)) (chartVec x z (stdVec b))) hround
  have hyentry (a b : Fin n) : gMat h y a b =
      (h y).toFun (chartVec y y (stdVec a)) (chartVec y y (stdVec b)) :=
    congrArg (fun z : M.Carrier =>
      (h z).toFun (chartVec y z (stdVec a)) (chartVec y z (stdVec b))) hself
  ext i j
  rw [hxentry]
  rw [chartVec_eq_centered_sum x y hy (stdVec i),
    chartVec_eq_centered_sum x y hy (stdVec j), hermitian_sum_left]
  simp only [hermitian_sum_right, HermitianInnerProduct.map_smul_left,
    HermitianInnerProduct.map_smul_right, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Finset.sum_mul, tangentFrameMatrix, hyentry]
  conv_rhs => rw [Finset.sum_comm]

theorem covectorCoords_eq_transpose_mulVec (x y : M.Carrier)
    (hy : y ∈ (extChartAt (ComplexModel n) x).source) (ξ : Covector n) :
    WithLp.ofLp (covectorCoords x y ξ) =
      (tangentFrameMatrix x y y)ᵀ *ᵥ WithLp.ofLp (covectorCoords y y ξ) := by
  ext i
  simpa only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, tangentFrameMatrix] using
    covectorCoords_transition y x y (mem_extChartAt_source _) hy ξ i

theorem dualNorm_eq_fixed_chart (h : HermitianField M) (x y : M.Carrier)
    (hy : y ∈ (extChartAt (ComplexModel n) x).source) (ξ : Covector n) :
    dualNorm h y ξ = dualNormChart h x (chartPt x y) (covectorCoords x y ξ) := by
  unfold dualNorm dualNormChart dualNormMat
  rw [hMat_eq_centered_congruence h x y hy, covectorCoords_eq_transpose_mulVec x y hy ξ]
  exact congrArg Complex.re (dual_quadratic_congruence (gMat h y) (tangentFrameMatrix x y y)
    (tangentFrameMatrix_isUnit x y hy) (WithLp.ofLp (covectorCoords y y ξ))).symm

theorem dualNorm_cotangentChartInv (h : HermitianField M) (x : M.Carrier)
    {z : CotangentCoord n} (hz : z ∈ cotangentTarget x) :
    dualNorm h (cotangentChartInv x z).1 (cotangentChartInv x z).2 =
      dualNormChart h x z.1 z.2 := by
  have hy := cotangentChartInv_mapsTo x hz
  rw [dualNorm_eq_fixed_chart h x (cotangentChartInv x z).1 hy]
  change dualNormChart h x (chartPt x (chartInv x z.1))
    (covectorCoords x (chartInv x z.1) (covectorOfCoords x (chartInv x z.1) z.2)) = _
  have hbase : chartPt x (chartInv x z.1) = z.1 := (extChartAt (ComplexModel n) x).right_inv hz.1
  have hys : chartInv x z.1 ∈ (extChartAt (ComplexModel n) x).source := hy
  rw [hbase, covectorCoords_ofCoords x (chartInv x z.1) hys z.2]

end Yau.Blueprint.V03Proof
