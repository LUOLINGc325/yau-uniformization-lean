import Yau.Proofs.E02RectCalculus

open Matrix Filter
open scoped Topology Matrix ComplexOrder Matrix.Norms.Elementwise
noncomputable section
namespace Yau.NodeProofs.E02Aux
open Yau Yau.Blueprint
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]

/-- Differentiate the genuine inverse identity. Differentiability of the
inverse field is established separately on its actual open unit locus. -/
theorem matrix_inv_fderiv_apply {n : ℕ} (H : D → Herm n) (x v : D)
    (hH : DifferentiableAt ℝ H x)
    (hI : DifferentiableAt ℝ (fun y => (H y)⁻¹) x)
    (hUnit : ∀ᶠ y in 𝓝 x, IsUnit (H y).det) :
    fderiv ℝ (fun y => (H y)⁻¹) x v = -((H x)⁻¹*fderiv ℝ H x v*(H x)⁻¹) := by
  have hx : IsUnit (H x).det := hUnit.self_of_nhds
  have hEq : (fun y => H y*(H y)⁻¹) =ᶠ[𝓝 x] (fun _ => (1 : Herm n)) := by
    filter_upwards [hUnit] with y hy
    exact Matrix.mul_nonsing_inv _ hy
  have hZero : fderiv ℝ (fun y => H y*(H y)⁻¹) x = 0 := by
    rw [hEq.fderiv_eq]
    exact fderiv_const_apply _
  have hProd := (rectMulCLM n n n).hasFDerivAt_of_bilinear hH.hasFDerivAt hI.hasFDerivAt
  have hDer := congrArg (fun L : D →L[ℝ] Herm n => L v) hProd.fderiv
  change (fderiv ℝ (fun y => H y*(H y)⁻¹) x) v =
    H x*fderiv ℝ (fun y => (H y)⁻¹) x v+fderiv ℝ H x v*(H x)⁻¹ at hDer
  rw [hZero] at hDer
  have hVal : H x*fderiv ℝ (fun y => (H y)⁻¹) x v+fderiv ℝ H x v*(H x)⁻¹ = 0 := by
    exact hDer.symm
  have hMul := congrArg (fun M : Herm n => (H x)⁻¹*M) hVal
  simp only [Matrix.mul_add,Matrix.mul_zero,←Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ hx,Matrix.one_mul] at hMul
  exact eq_neg_of_add_eq_zero_left hMul

end Yau.NodeProofs.E02Aux
