import Yau.Proofs.G01ComplexMetricDerivative

noncomputable section
open scoped Matrix
namespace Yau.NodeProofs.G01Aux
open Yau Yau.LeafProofs
variable {n : ℕ}

/-- Differentiation of raw realification is entrywise real differentiation, without a Hermitian hypothesis. -/
theorem rawReal_derivative (A : ComplexVector n → Matrix (Fin n) (Fin n) ℂ)
    (z : ComplexVector n) (hA : ∀ i j, DifferentiableAt ℝ (fun w => A w i j) z)
    (a : RIdx n) :
    L12Aux.matrixDirectionalDerivative (fun w => rawReal (A w)) z (realVec a) =
      rawReal (matrixRealDerivative A z a) := by
  ext ⟨i, b⟩ ⟨j, c⟩
  have hR : fderiv ℝ (fun w => (A w i j).re) z =
      Complex.reCLM.comp (fderiv ℝ (fun w => A w i j) z) :=
    (Complex.reCLM.hasFDerivAt.comp z (hA i j).hasFDerivAt).fderiv
  have hI : fderiv ℝ (fun w => (A w i j).im) z =
      Complex.imCLM.comp (fderiv ℝ (fun w => A w i j) z) :=
    (Complex.imCLM.hasFDerivAt.comp z (hA i j).hasFDerivAt).fderiv
  fin_cases b <;> fin_cases c <;>
    simp [L12Aux.matrixDirectionalDerivative, rawReal, matrixRealDerivative,
      fderiv_fun_neg, hR, hI]

end Yau.NodeProofs.G01Aux
