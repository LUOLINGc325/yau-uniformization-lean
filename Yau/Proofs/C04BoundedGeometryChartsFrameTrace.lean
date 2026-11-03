import Yau.Proofs.C04BoundedGeometryChartsNormalModels
import Yau.Proofs.C04HermitianHessianTrace

/-! The genuine real frame trace in fixed real coordinate coefficients. -/
noncomputable section
open scoped Topology ContDiff Matrix.Norms.Elementwise
namespace Yau.Proofs.C04ChartsAux
open Yau Yau.LeafProofs.L12Aux
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 5

def framePrincipalCoefficients (B : ComplexVector n →L[ℝ] ComplexVector n) :
    Matrix (RIdx n) (RIdx n) ℝ := fun i j =>
  (1 / 2 : ℝ) * ∑ c : RIdx n, realCoord (B (realVec c)) i * realCoord (B (realVec c)) j

def frameDriftCoefficients (B : ComplexVector n →L[ℝ] ComplexVector n)
    (G : ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n) : RIdx n → ℝ := fun k =>
  - ∑ i, ∑ j, framePrincipalCoefficients B i j * realCoord (G (realVec i) (realVec j)) k

theorem complexBilin_eq_sum
    (H : ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ℂ) (u v : ComplexVector n) :
    H u v = ∑ i : RIdx n, ∑ j : RIdx n,
      (realCoord u i : ℂ) * (realCoord v j : ℂ) * H (realVec i) (realVec j) := by
  let Hr : ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ℝ :=
    (ContinuousLinearMap.compL ℝ (ComplexVector n) ℂ ℝ Complex.reCLM).comp H
  let Hi : ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ℝ :=
    (ContinuousLinearMap.compL ℝ (ComplexVector n) ℂ ℝ Complex.imCLM).comp H
  apply Complex.ext
  · simpa only [Complex.re_sum, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, zero_mul, sub_zero, zero_add, Hr,
      ContinuousLinearMap.compL_apply, ContinuousLinearMap.comp_apply, Complex.reCLM_apply] using
      realBilin_eq_sum Hr u v
  · simpa only [Complex.im_sum, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, zero_mul, sub_zero, zero_add, add_zero, Hi,
      ContinuousLinearMap.compL_apply, ContinuousLinearMap.comp_apply, Complex.imCLM_apply] using
      realBilin_eq_sum Hi u v

theorem complexBilin_frame_trace
    (H : ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ℂ)
    (B : ComplexVector n →L[ℝ] ComplexVector n) :
    (∑ i : RIdx n, ∑ j : RIdx n,
      (framePrincipalCoefficients B i j : ℂ) * H (realVec i) (realVec j)) =
      (1 / 2 : ℂ) * ∑ c : RIdx n, H (B (realVec c)) (B (realVec c)) := by
  symm
  have hexp : (∑ c : RIdx n, H (B (realVec c)) (B (realVec c))) =
      ∑ c : RIdx n, ∑ i : RIdx n, ∑ j : RIdx n,
        (realCoord (B (realVec c)) i : ℂ) * (realCoord (B (realVec c)) j : ℂ) * H (realVec i) (realVec j) :=
    Finset.sum_congr rfl (fun c hc => complexBilin_eq_sum H _ _)
  rw [hexp]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp only [framePrincipalCoefficients, Complex.ofReal_mul, Complex.ofReal_div,
    Complex.ofReal_one, Complex.ofReal_ofNat, Complex.ofReal_sum, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro c _
  ring

end Yau.Proofs.C04ChartsAux
