import Yau.Proofs.F01LogDetDifferential

/-! Transfer the accepted determinant differential through the genuine
finite-dimensional identity into the original Frobenius matrix norm. The
inverse trace and the underlying matrix derivative are unchanged. -/
noncomputable section
open scoped Matrix ComplexOrder Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def frobeniusToComplexEntriesCLM : Matrix (Fin n) (Fin n) ℂ →L[ℝ] (Fin n → Fin n → ℂ) :=
  LinearMap.toContinuousLinearMap (𝕜 := ℝ)
    (E := Matrix (Fin n) (Fin n) ℂ) (F' := Fin n → Fin n → ℂ)
    { toFun := fun H i j => H i j
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

theorem frobenius_logdet_fderiv_trace (H : E → Matrix (Fin n) (Fin n) ℂ) (z v : E)
    (hH : DifferentiableAt ℝ H z) (hpos : (H z).PosDef) :
    fderiv ℝ (fun w => Real.log (H w).det.re) z v = traceWith (H z) (fderiv ℝ H z v) := by
  let J := frobeniusToComplexEntriesCLM (n := n)
  have hd : HasFDerivAt (fun w => J (H w)) (J.comp (fderiv ℝ H z)) z :=
    J.hasFDerivAt.comp z hH.hasFDerivAt
  have hj : DifferentiableAt ℝ (fun w => J (H w)) z := hd.differentiableAt
  have h := logdet_fderiv_trace (fun w => J (H w)) z v hj hpos
  have he : fderiv ℝ (fun w => J (H w)) z v = J (fderiv ℝ H z v) :=
    congrArg (fun D : E →L[ℝ] (Fin n → Fin n → ℂ) => D v) hd.fderiv
  erw [he] at h
  exact h

end Yau.NodeProofs.F01Aux
