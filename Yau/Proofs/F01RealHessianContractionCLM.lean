import Yau.Proofs.F01HolderBilinear
import Yau.Proofs.F01ComplexHeatRealification
import Yau.LeafProofs.L17RicciMatrixHolder

/-! The actual real Hessian contraction is a bounded bilinear map in
the original Frobenius matrix and operator Hessian norms. Its Holder bound
therefore controls the genuine scalar forcing, rather than an oracle source. -/
noncomputable section
open scoped ContDiff Matrix Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic Yau.LeafProofs.L17Aux
variable {n : ℕ}

def realFrobeniusEntryCLM (a b : RIdx n) : Mat n →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := Mat n) (F' := ℝ)
    { toFun := fun A => A a b
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

def hessianPairEvaluationCLM (a b : RIdx n) :
    (Space n →L[ℝ] Space n →L[ℝ] ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.apply ℝ ℝ (realVec b)).comp
    (ContinuousLinearMap.apply ℝ (Space n →L[ℝ] ℝ) (realVec a))

def realHessianContractionCLM :
    Mat n →L[ℝ] (Space n →L[ℝ] Space n →L[ℝ] ℝ) →L[ℝ] ℝ :=
  ∑ a, ∑ b, (realFrobeniusEntryCLM a b).smulRight (hessianPairEvaluationCLM a b)

theorem realHessianContractionCLM_apply (A : Mat n)
    (B : Space n →L[ℝ] Space n →L[ℝ] ℝ) :
    realHessianContractionCLM A B = ∑ a, ∑ b, A a b * B (realVec a) (realVec b) := by
  simp only [realHessianContractionCLM, sum_apply, ContinuousLinearMap.smulRight_apply,
    smul_apply, smul_eq_mul]
  rfl

theorem realHessianContractionCLM_eq_complex_trace
    (H : Matrix (Fin n) (Fin n) ℂ) {q : Space n → ℝ} {z : Space n}
    (hq : ContDiffAt ℝ 2 q z) :
    realHessianContractionCLM (scalarSymbol H) (fderiv ℝ (fderiv ℝ q) z) =
      traceWith H (leviC q z) := by
  rw [traceWith_levi_eq_scalarSymbol H hq, realHessianContractionCLM_apply]
  rfl

theorem native_background_source_contraction
    (H : Matrix (Fin n) (Fin n) ℂ) (A : Space n → Matrix (Fin n) (Fin n) ℂ)
    {z : Space n} (hA : ContDiffAt ℝ 2 (fun w => Real.log (A w).det.re) z) :
    -traceWith H (backgroundRicci A z) =
      realHessianContractionCLM (scalarSymbol H)
        (fderiv ℝ (fderiv ℝ (fun w => Real.log (A w).det.re)) z) := by
  rw [realHessianContractionCLM_eq_complex_trace H hA]
  simp only [backgroundRicci, traceWith, Matrix.mul_neg, Matrix.trace_neg, Complex.neg_re, neg_neg]

end Yau.NodeProofs.F01Aux
