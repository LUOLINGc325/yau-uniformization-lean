import Yau.Proofs.G01ChernCalculus
import Yau.Proofs.G01RawAlgebra
import Yau.Proofs.G01ConnectionJ

noncomputable section
open Filter
open scoped Manifold Topology ContDiff Matrix ComplexOrder
namespace Yau.NodeProofs.G01Aux
set_option backward.isDefEq.respectTransparency false
open Yau Yau.LeafProofs
variable {n r : ℕ}

def matrixRealDerivative (H : ComplexVector n → Matrix (Fin r) (Fin r) ℂ)
    (z : ComplexVector n) (a : RIdx n) : Matrix (Fin r) (Fin r) ℂ :=
  fun i j => fderiv ℝ (fun w => H w i j) z (realVec a)

theorem matrixRealDerivative_zero (H : ComplexVector n → Matrix (Fin r) (Fin r) ℂ)
    (z : ComplexVector n) (k : Fin n) :
    matrixRealDerivative H z (k, 0) = matrixWirt H z k + matrixWirtBar H z k := by
  ext i j
  simp only [matrixRealDerivative, realVec, matrixWirt, matrixWirtBar, Matrix.add_apply,
    wirt, wirtBar]
  simp only [ite_true, one_smul, stdVec]
  ring

theorem matrixRealDerivative_one (H : ComplexVector n → Matrix (Fin r) (Fin r) ℂ)
    (z : ComplexVector n) (k : Fin n) :
    matrixRealDerivative H z (k, 1) =
      Complex.I • (matrixWirt H z k - matrixWirtBar H z k) := by
  ext i j
  simp only [matrixRealDerivative, realVec, matrixWirt, matrixWirtBar, Matrix.sub_apply,
    Matrix.smul_apply, smul_eq_mul, wirt, wirtBar]
  simp only [Fin.reduceEq, ite_false, stdVec]
  linear_combination fderiv ℝ (fun w => H w i j) z (Complex.I • EuclideanSpace.single k 1) * Complex.I_sq

variable {M : ComplexManifold n}

theorem matrixWirtBar_hMat (h : HermitianField M) (x : M.Carrier)
    (z : ComplexVector n) (k : Fin n) :
    matrixWirtBar (hMat h x) z k = (matrixWirt (hMat h x) z k)ᴴ := by
  ext i j
  have he : (fun w => hMat h x w i j) = (fun w => star (hMat h x w j i)) := by
    funext w
    exact (L12Aux.hMat_isHermitian h x w).apply i j |>.symm
  simp only [matrixWirtBar, matrixWirt, Matrix.conjTranspose_apply]
  rw [he, L14Aux.wirtBar_star]

/-- The actual real derivative of the raw representation is the raw derivative. -/
theorem realMetricFn_derivative_eq (h : HermitianField M) (hs : MetricSmooth h)
    (x : M.Carrier) (z : ComplexVector n) (hz : z ∈ chartTarget x) (a : RIdx n) :
    L12Aux.matrixDirectionalDerivative (fun w => realMetricFn h x w) z (realVec a) =
      (2 : ℝ) • rawReal (matrixRealDerivative (hMat h x) z a) := by
  ext ⟨i, b⟩ ⟨j, c⟩
  have hH : DifferentiableAt ℝ (fun w => hMat h x w i j) z :=
    ((L17Aux.hMat_contDiffOn_of_metricSmooth h hs x i j).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).differentiableAt (by simp)
  have hR : fderiv ℝ (fun w => (hMat h x w i j).re) z =
      Complex.reCLM.comp (fderiv ℝ (fun w => hMat h x w i j) z) :=
    (Complex.reCLM.hasFDerivAt.comp z hH.hasFDerivAt).fderiv
  have hI : fderiv ℝ (fun w => (hMat h x w i j).im) z =
      Complex.imCLM.comp (fderiv ℝ (fun w => hMat h x w i j) z) :=
    (Complex.imCLM.hasFDerivAt.comp z hH.hasFDerivAt).fderiv
  have hRdiff : DifferentiableAt ℝ (fun w => (hMat h x w i j).re) z :=
    Complex.reCLM.differentiableAt.comp z hH
  have hIdiff : DifferentiableAt ℝ (fun w => (hMat h x w i j).im) z :=
    Complex.imCLM.differentiableAt.comp z hH
  have hR2 : fderiv ℝ (fun w => 2 * (hMat h x w i j).re) z =
      (2 : ℝ) • (Complex.reCLM.comp (fderiv ℝ (fun w => hMat h x w i j) z)) := by
    rw [fderiv_const_mul hRdiff 2, hR]
  have hI2 : fderiv ℝ (fun w => 2 * (hMat h x w i j).im) z =
      (2 : ℝ) • (Complex.imCLM.comp (fderiv ℝ (fun w => hMat h x w i j) z)) := by
    rw [fderiv_const_mul hIdiff 2, hI]
  fin_cases b <;> fin_cases c <;>
    simp [L12Aux.matrixDirectionalDerivative, L12Aux.realMetricFn_entries,
      Matrix.smul_apply, smul_eq_mul, rawReal, matrixRealDerivative,
      fderiv_fun_neg, hR2, hI2]

end Yau.NodeProofs.G01Aux
