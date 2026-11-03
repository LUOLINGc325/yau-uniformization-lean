import Yau.Proofs.E01QuadraticFirst

/-! The full mixed derivative of a quadratic fiber summand, before finite contraction. -/

noncomputable section
open scoped Topology
open Filter

namespace Yau.NodeProofs.E01Aux
open Yau
open Yau.Blueprint.V03Proof

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem mixedWirt_quadratic_summand (L R : E →L[ℂ] ℂ) {F : E → ℂ} {z : E}
    (hF : ContDiffAt ℝ 2 F z) (v : E) :
    wirt (fun w => wirtBar (fun y => star (L y) * F y * R y) w v) z v =
      star (L v) * F z * R v + star (L v) * wirt F z v * R z +
      star (L z) * wirtBar F z v * R v +
      star (L z) * wirt (fun w => wirtBar F w v) z v * R z := by
  have hFd : DifferentiableAt ℝ F z := hF.differentiableAt (by norm_num)
  have hRd : DifferentiableAt ℝ (fun w => R w) z := R.differentiableAt.restrictScalars ℝ
  have hLd : DifferentiableAt ℝ (fun w => star (L w)) z :=
    Complex.conjCLE.differentiableAt.comp z (L.differentiableAt.restrictScalars ℝ)
  have hbar : DifferentiableAt ℝ (fun w => wirtBar F w v) z := wirtBar_differentiableAt hF v
  have heq : (fun w => wirtBar (fun y => star (L y) * F y * R y) w v) =ᶠ[𝓝 z]
      (fun w => star (L v) * F w * R w + star (L w) * wirtBar F w v * R w) := by
    filter_upwards [hF.eventually (by norm_num)] with w hw
    exact wirtBar_quadratic_summand L R (hw.differentiableAt (by norm_num)) v
  have hconst : DifferentiableAt ℝ (fun _ : E => star (L v)) z := differentiableAt_const _
  have h₁ : DifferentiableAt ℝ (fun w => star (L v) * F w * R w) z :=
    (hconst.mul hFd).mul hRd
  have h₂ : DifferentiableAt ℝ (fun w => star (L w) * wirtBar F w v * R w) z :=
    (hLd.mul hbar).mul hRd
  have hw : wirt (fun w => wirtBar (fun y => star (L y) * F y * R y) w v) z v =
      wirt (fun w => star (L v) * F w * R w + star (L w) * wirtBar F w v * R w) z v := by
    unfold wirt
    rw [heq.fderiv_eq]
  have hc : wirt (fun _ : E => star (L v)) z v = 0 := by simp [wirt]
  rw [hw, wirt_add _ _ z v h₁ h₂,
    wirt_mul (f := fun w => star (L v) * F w) (g := fun w => R w)
      (hconst.mul hFd) hRd,
    wirt_mul hconst hFd, hc, wirt_complex_linear,
    wirt_quadratic_summand L R hbar v]
  ring

end Yau.NodeProofs.E01Aux
