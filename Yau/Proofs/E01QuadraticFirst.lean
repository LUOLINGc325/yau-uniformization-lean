import Yau.Proofs.V03LeviCalculus

/-! First Wirtinger derivatives of an actual quadratic fiber summand. -/

noncomputable section
open scoped Topology

namespace Yau.NodeProofs.E01Aux
open Yau
open Yau.Blueprint.V03Proof

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem wirt_complex_linear (L : E →L[ℂ] ℂ) (z v : E) :
    wirt L z v = L v := by
  rw [wirt_holomorphic L.differentiableAt]
  rw [L.hasFDerivAt.fderiv]

theorem wirtBar_complex_linear (L : E →L[ℂ] ℂ) (z v : E) :
    wirtBar L z v = 0 := wirtBar_holomorphic L.differentiableAt v

theorem wirt_quadratic_summand (L R : E →L[ℂ] ℂ) {F : E → ℂ} {z : E}
    (hF : DifferentiableAt ℝ F z) (v : E) :
    wirt (fun w => star (L w) * F w * R w) z v =
      star (L z) * wirt F z v * R z + star (L z) * F z * R v := by
  have hL : DifferentiableAt ℝ (fun w => star (L w)) z :=
    Complex.conjCLE.differentiableAt.comp z (L.differentiableAt.restrictScalars ℝ)
  have hR : DifferentiableAt ℝ (fun w => R w) z := R.differentiableAt.restrictScalars ℝ
  rw [wirt_mul (f := fun w => star (L w) * F w) (g := fun w => R w)
      (hL.mul hF) hR, wirt_mul hL hF,
    wirt_conj, wirtBar_complex_linear, star_zero, wirt_complex_linear]
  ring

theorem wirtBar_quadratic_summand (L R : E →L[ℂ] ℂ) {F : E → ℂ} {z : E}
    (hF : DifferentiableAt ℝ F z) (v : E) :
    wirtBar (fun w => star (L w) * F w * R w) z v =
      star (L v) * F z * R z + star (L z) * wirtBar F z v * R z := by
  have hL : DifferentiableAt ℝ (fun w => star (L w)) z :=
    Complex.conjCLE.differentiableAt.comp z (L.differentiableAt.restrictScalars ℝ)
  have hR : DifferentiableAt ℝ (fun w => R w) z := R.differentiableAt.restrictScalars ℝ
  rw [wirtBar_mul (f := fun w => star (L w) * F w) (g := fun w => R w)
      (hL.mul hF) hR, wirtBar_mul hL hF,
    wirtBar_conj, wirt_complex_linear, wirtBar_complex_linear]
  ring

end Yau.NodeProofs.E01Aux
