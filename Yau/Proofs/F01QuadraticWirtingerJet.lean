import Yau.Proofs.F01QuadraticJacobian

/-! Native unbarred derivatives of the actual holomorphic Jacobian. -/
noncomputable section
namespace Yau.NodeProofs.F01Aux
open Yau

theorem wirt_of_complex_differentiable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : E → ℂ} {z : E} (hf : DifferentiableAt ℂ f z) (v : E) :
    wirt f z v = fderiv ℂ f z v := by
  unfold wirt
  rw [hf.fderiv_restrictScalars (𝕜 := ℝ)]
  change (1 / 2 : ℂ) * (fderiv ℂ f z v - Complex.I * fderiv ℂ f z (Complex.I • v)) = _
  rw [map_smul, smul_eq_mul, ← mul_assoc, Complex.I_mul_I]
  ring

theorem quadraticJacobian_entry_wirt {n : ℕ}
    (B : ComplexVector n →L[ℂ] ComplexVector n →L[ℂ] ComplexVector n)
    (hB : ∀ v w, B v w = B w v) (z v : ComplexVector n) (i j : Fin n) :
    wirt (fun w => quadraticJacobian B w i j) z v = B v (stdVec j) i := by
  rw [wirt_of_complex_differentiable (quadraticJacobian_entry_differentiableAt B z i j),
    quadraticJacobian_entry_fderiv B hB]

end Yau.NodeProofs.F01Aux
