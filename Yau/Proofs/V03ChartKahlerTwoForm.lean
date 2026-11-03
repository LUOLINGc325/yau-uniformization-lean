import Yau.Proofs.V03MatrixKahlerInvariance
import Yau.Proofs.V03MetricQuadratic
import Yau.Proofs.V03AreaNormalization

/-! The actual chart metric defines a native real alternating Kähler
two-form, with exactly the original coefficient and area normalization. -/

open scoped Manifold Topology ContDiff Matrix

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

variable {n : ℕ} {M : ComplexManifold n}

theorem chartVec_complex_basis_sum (x y : M.Carrier) (u : ComplexVector n) :
    (∑ i, u i • chartVec x y (stdVec i)) = chartVec x y u := by
  have hu : (∑ i, u i • stdVec i) = u := by
    ext i
    simp [stdVec, EuclideanSpace.single, Pi.single_apply]
  simpa only [chartVec_sum, chartVec_smul] using congrArg (chartVec x y) hu

theorem hMat_pair (h : HermitianField M) (x : M.Carrier) (z u v : ComplexVector n) :
    star (fun i => u i) ⬝ᵥ (hMat h x z *ᵥ fun i => v i) =
      (h (chartInv x z)).toFun (chartVec x (chartInv x z) u) (chartVec x (chartInv x z) v) := by
  rw [← chartVec_complex_basis_sum x (chartInv x z) u,
    ← chartVec_complex_basis_sum x (chartInv x z) v, hermitian_sum_left]
  simp only [hermitian_sum_right, HermitianInnerProduct.map_smul_left,
    HermitianInnerProduct.map_smul_right, dotProduct, Matrix.mulVec, Pi.star_apply,
    Finset.mul_sum, hMat]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

def chartKahlerTwoForm (h : HermitianField M) (x : M.Carrier) (z : ComplexVector n) :
    ComplexVector n [⋀^Fin 2]→L[ℝ] ℝ := matrixKahlerTwoForm (hMat h x z)

theorem chartKahlerTwoForm_apply (h : HermitianField M) (x : M.Carrier) (z u v : ComplexVector n) :
    chartKahlerTwoForm h x z ![u, v] =
      2 * ((h (chartInv x z)).toFun (chartVec x (chartInv x z) u)
        (chartVec x (chartInv x z) v)).im := by
  rw [chartKahlerTwoForm, matrixKahlerTwoForm_apply (hMat_isHermitian h x z), hMat_pair]

theorem chartKahlerTwoForm_realVec (h : HermitianField M) (x : M.Carrier)
    (z : ComplexVector n) (a b : RIdx n) :
    chartKahlerTwoForm h x z ![realVec a, realVec b] = kahlerFormFn h x z a b :=
  chartKahlerTwoForm_apply h x z _ _

theorem chartKahlerTwoForm_J (h : HermitianField M) (x : M.Carrier) (z u v : ComplexVector n) :
    chartKahlerTwoForm h x z ![Complex.I • u, Complex.I • v] = chartKahlerTwoForm h x z ![u, v] :=
  matrixKahlerTwoForm_J (hMat_isHermitian h x z) u v

theorem chartKahlerTwoForm_contDiffOn (g : SmoothMetric M) (x : M.Carrier) :
    ContDiffOn ℝ ∞ (chartKahlerTwoForm g.form x) (chartTarget x) :=
  matrixKahlerTwoForm_contDiffOn (hMat_contDiffOn g x)

end Yau.Blueprint.V03Proof
