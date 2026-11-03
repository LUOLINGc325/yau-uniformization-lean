import Yau.Proofs.V04WallErrorQuadraticBlocks
import Yau.Proofs.V04WallErrorKahler
import Yau.Proofs.V04WallErrorPlateau

/-! The preceding fiber quadratic calculation is the genuine dual norm
of the metric in the same valid chart. -/

open Filter
open scoped Manifold Topology ContDiff Matrix ComplexOrder
noncomputable section
namespace Yau.Blueprint.V04Proof.WallErrorAux
open Yau Yau.Blueprint V03Proof Yau.NodeProofs.G01Aux

variable {n : ℕ} {M : ComplexManifold n}

def normChartHessian (h : HermitianField M) (x : M.Carrier) (p : CotangentCoord n) : CotangentMatrix n :=
  leviMatrix (fun z => dualNormChart h x z.1 z.2) p cotangentDir

theorem dualNormChart_eq_re_complexQuadratic (h : HermitianField M) (x : M.Carrier)
    (p : CotangentCoord n) :
    dualNormChart h x p.1 p.2 =
      (complexQuadratic (fun z => ((hMat h x z)⁻¹)ᵀ) p).re := by
  simp only [dualNormChart, dualNormMat, complexQuadratic, dotProduct,
    Matrix.mulVec, Pi.star_apply, Matrix.transpose_apply, Finset.mul_sum, mul_assoc]

theorem inverseMetric_entry_contDiffAt (h : HermitianField M) (hs : MetricSmooth h)
    (x : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget x) (a b : Fin n) :
    ContDiffAt ℝ 2 (fun w => (hMat h x w)⁻¹ a b) z := by
  have hH := Yau.LeafProofs.L17Aux.hMat_contDiffOn_of_metricSmooth h hs x
  exact ((entrywise_matrix_inv_contDiffOn hH
    (fun w hw => (hMat_posDef h x w hw).det_pos.ne') a b).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).of_le (by simp)

theorem normChartHessian_horizontal (h : HermitianField M) (hs : MetricSmooth h)
    (x : M.Carrier) {p : CotangentCoord n} (hp : p.1 ∈ chartTarget x) (i j : Fin n) :
    normChartHessian h x p (Sum.inl i) (Sum.inl j) =
      ∑ a, ∑ b, star (p.2 a) *
        wirt (fun z => wirtBar (fun u => (hMat h x u)⁻¹ b a) z (stdVec i)) p.1 (stdVec j) * p.2 b := by
  have hHerm (z : ComplexVector n) (_ : z ∈ (Set.univ : Set (ComplexVector n))) :
      (((hMat h x z)⁻¹)ᵀ).IsHermitian := (hMat_isHermitian h x z).inv.transpose
  have hA (a b : Fin n) : ContDiffAt ℝ 2 (fun z => (((hMat h x z)⁻¹)ᵀ) a b) p.1 :=
    inverseMetric_entry_contDiffAt h hs x hp b a
  have heq : (fun z : CotangentCoord n => dualNormChart h x z.1 z.2) =
      (fun z => (complexQuadratic (fun w => ((hMat h x w)⁻¹)ᵀ) z).re) :=
    funext (dualNormChart_eq_re_complexQuadratic h x)
  unfold normChartHessian
  rw [heq, leviMatrix_re_complexQuadratic_entry isOpen_univ hHerm (Set.mem_univ _) (Sum.inl i) (Sum.inl j)]
  exact quadraticHessian_horizontal hA i j

theorem normChartHessian_vertical (h : HermitianField M) (hs : MetricSmooth h)
    (x : M.Carrier) {p : CotangentCoord n} (hp : p.1 ∈ chartTarget x) (i j : Fin n) :
    normChartHessian h x p (Sum.inr i) (Sum.inr j) = (hMat h x p.1)⁻¹ j i := by
  have hHerm (z : ComplexVector n) (_ : z ∈ (Set.univ : Set (ComplexVector n))) :
      (((hMat h x z)⁻¹)ᵀ).IsHermitian := (hMat_isHermitian h x z).inv.transpose
  have hA (a b : Fin n) : ContDiffAt ℝ 2 (fun z => (((hMat h x z)⁻¹)ᵀ) a b) p.1 :=
    inverseMetric_entry_contDiffAt h hs x hp b a
  have heq : (fun z : CotangentCoord n => dualNormChart h x z.1 z.2) =
      (fun z => (complexQuadratic (fun w => ((hMat h x w)⁻¹)ᵀ) z).re) :=
    funext (dualNormChart_eq_re_complexQuadratic h x)
  unfold normChartHessian
  rw [heq, leviMatrix_re_complexQuadratic_entry isOpen_univ hHerm (Set.mem_univ _) (Sum.inr i) (Sum.inr j)]
  exact quadraticHessian_vertical hA i j

theorem normChartHessian_mixed (h : HermitianField M) (hs : MetricSmooth h)
    (x : M.Carrier) {p : CotangentCoord n} (hp : p.1 ∈ chartTarget x) (i j : Fin n) :
    normChartHessian h x p (Sum.inl i) (Sum.inr j) =
      ∑ a, star (p.2 a) * wirtBar (fun z => (hMat h x z)⁻¹ j a) p.1 (stdVec i) := by
  have hHerm (z : ComplexVector n) (_ : z ∈ (Set.univ : Set (ComplexVector n))) :
      (((hMat h x z)⁻¹)ᵀ).IsHermitian := (hMat_isHermitian h x z).inv.transpose
  have hA (a b : Fin n) : ContDiffAt ℝ 2 (fun z => (((hMat h x z)⁻¹)ᵀ) a b) p.1 :=
    inverseMetric_entry_contDiffAt h hs x hp b a
  have heq : (fun z : CotangentCoord n => dualNormChart h x z.1 z.2) =
      (fun z => (complexQuadratic (fun w => ((hMat h x w)⁻¹)ᵀ) z).re) :=
    funext (dualNormChart_eq_re_complexQuadratic h x)
  unfold normChartHessian
  rw [heq, leviMatrix_re_complexQuadratic_entry isOpen_univ hHerm (Set.mem_univ _) (Sum.inl i) (Sum.inr j)]
  exact quadraticHessian_mixed hA i j

theorem spatialHessian_dualNorm_eq_normChartHessian {X : KahlerManifold n}
    (h : HermitianField X.manifold) (y : CotangentPoint X.manifold) :
    spatialHessian (fun y' => dualNorm h y'.1 y'.2) y = normChartHessian h y.1 (cotangentChart y.1 y) := by
  have hopen : IsOpen (cotangentTarget y.1) :=
    (isOpen_extChartAt_target (I := ComplexModel n) y.1).prod isOpen_univ
  have hy : y ∈ cotangentSource y.1 := mem_extChartAt_source y.1
  have heq : (fun z => dualNorm h (cotangentChartInv y.1 z).1 (cotangentChartInv y.1 z).2) =ᶠ[𝓝 (cotangentChart y.1 y)]
      (fun z => dualNormChart h y.1 z.1 z.2) := by
    filter_upwards [hopen.mem_nhds (cotangentChart_mapsTo y.1 hy)] with z hz
    exact dualNorm_cotangentChartInv h y.1 hz
  exact leviMatrix_congr_of_eventuallyEq heq cotangentDir

end Yau.Blueprint.V04Proof.WallErrorAux
