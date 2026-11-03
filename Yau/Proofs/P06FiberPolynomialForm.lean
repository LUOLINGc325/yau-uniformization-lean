import Yau.Proofs.P06FiberPolynomialAlgebra
import Yau.Proofs.G04SignedFormInverse
import Yau.Proofs.G04RicciForm

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
namespace Yau.NodeProofs.P06Aux.FiberPoly
open Yau Yau.LeafProofs G04Aux
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {M : ComplexManifold n}

/-- The central Hermitian matrix prescribed by the original metric and actual two-form. -/
def fiberMatrix (h : HermitianField M) (A : RealForm M 2) (p : Polynomial ℝ)
    (x : M.Carrier) : Matrix (Fin n) (Fin n) ℂ :=
  gMat h x * Polynomial.aeval ((gMat h x)⁻¹ * formHermitianMatrix A x) p

theorem fiberMatrix_hermitian (h : HermitianField M) (A : RealForm M 2)
    (h11 : RealOneOne A) (p : Polynomial ℝ) (x : M.Carrier) :
    (fiberMatrix h A p x).IsHermitian :=
  weighted_aeval_hermitian _ _ (L12Aux.hMat_isHermitian h x (chartPt x x))
    ((representsSelf A h11).2 x)
    ((L12Aux.hMat_posDef h x (chartPt x x) (mem_extChartAt_target x)).isUnit.map
      Matrix.detMonoidHom) p

/-- The actual real alternating two-form reconstructed by the G04 iota map. -/
def polynomialForm (h : HermitianField M) (A : RealForm M 2) (h11 : RealOneOne A)
    (p : Polynomial ℝ) : RealForm M 2 :=
  iotaRealForm (fiberMatrix h A p) (fiberMatrix_hermitian h A h11 p)

theorem polynomialForm_oneOne (h : HermitianField M) (A : RealForm M 2)
    (h11 : RealOneOne A) (p : Polynomial ℝ) :
    RealOneOne (polynomialForm h A h11 p) :=
  iotaRealForm_oneOne _ _

theorem polynomialForm_matrix (h : HermitianField M) (A : RealForm M 2)
    (h11 : RealOneOne A) (p : Polynomial ℝ) (x : M.Carrier) :
    formHermitianMatrix (polynomialForm h A h11 p) x = fiberMatrix h A p x :=
  formHermitianMatrix_of_representsIota _ _ (iotaRealForm_represents _ _) x

/-- The actual Hermitian matrix of a two-form in a possibly noncentral chart. -/
def chartHermitianMatrix (A : RealForm M 2) (c : M.Carrier) (z : ComplexVector n) :
    Matrix (Fin n) (Fin n) ℂ :=
  let y := chartInv c z
  let D := L17Aux.linearMatrix (L17Aux.coordinateDifferential (inverseChart c) y z)
  Dᴴ * formHermitianMatrix A y * D

theorem chartHermitianMatrix_represents (A : RealForm M 2) (h11 : RealOneOne A)
    (c : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget c)
    (u v : ComplexVector n) :
    L03.chartForm A c z ![u,v] = 2 * (matrixPairing (chartHermitianMatrix A c z) u v).im := by
  have hD (w : ComplexVector n) :
      L17Aux.coordinateDifferential (inverseChart c) (chartInv c z) z w =
        tangentCoords (chartInv c z) (chartInv c z) (chartVec c (chartInv c z) w) := by
    rw [chartVec_inverseChart c hz]
    rfl
  rw [chartForm_apply_two]
  simp only [chartHermitianMatrix, matrixPairing_congruence, hD]
  simpa only [matrixPairing, L12Aux.chartVec_tangentCoords _ _ (mem_extChartAt_source _)] using
    (representsSelf A h11).1 (chartInv c z)
      (tangentCoords (chartInv c z) (chartInv c z) (chartVec c (chartInv c z) u))
      (tangentCoords (chartInv c z) (chartInv c z) (chartVec c (chartInv c z) v))

theorem chartHermitianMatrix_raw (A : RealForm M 2) (h11 : RealOneOne A)
    (c : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget c) :
    chartFormMatrix A c z = (-2 : ℝ) •
      (G01Aux.rawReal (chartHermitianMatrix A c z) * L12Aux.jMatrix n) := by
  ext a b
  rw [chartFormMatrix_apply, chartHermitianMatrix_represents A h11 c hz]
  exact matrixImagBilin_basis_raw _ a b

theorem metric_chart_congruence (h : HermitianField M) (c : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget c) :
    hMat h c z =
      let y := chartInv c z
      let D := L17Aux.linearMatrix (L17Aux.coordinateDifferential (inverseChart c) y z)
      Dᴴ * gMat h y * D := by
  rw [← pullbackMatrix_inverseChart h c hz]
  exact L17Aux.pullbackMatrix_eq_congruence h (inverseChart c) (chartInv c z) z
    (mem_extChartAt_source _)

/-- The central construction has the correct polynomial formula in every chart. -/
theorem chartHermitianMatrix_polynomialForm (h : HermitianField M) (A : RealForm M 2)
    (h11 : RealOneOne A) (p : Polynomial ℝ) (c : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget c) :
    chartHermitianMatrix (polynomialForm h A h11 p) c z =
      hMat h c z * Polynomial.aeval ((hMat h c z)⁻¹ * chartHermitianMatrix A c z) p := by
  let y := chartInv c z
  let D := L17Aux.linearMatrix (L17Aux.coordinateDifferential (inverseChart c) y z)
  have hD : IsUnit D.det := isUnit_iff_ne_zero.mpr
    (L17Aux.linearMatrix_det_ne_zero _ (L17Aux.coordinateDifferential_injective
      (inverseChart c) (inverseChart_differentiable c) (inverseChart_inverse_differentiable c)
      y (show z ∈ (inverseChart c).source by rw [inverseChart_source]; exact hz)
      (mem_extChartAt_source y)))
  simp only [metric_chart_congruence h c hz]
  change Dᴴ * formHermitianMatrix (polynomialForm h A h11 p) y * D =
    (Dᴴ * gMat h y * D) * Polynomial.aeval
      ((Dᴴ * gMat h y * D)⁻¹ * (Dᴴ * formHermitianMatrix A y * D)) p
  rw [polynomialForm_matrix, fiberMatrix, weighted_aeval_congruence p _ _ _ hD]

end Yau.NodeProofs.P06Aux.FiberPoly
