import Yau.Proofs.E02AffinePullback
import Yau.Proofs.E02LeviBilinear
import Yau.Proofs.E02LowerTestJet

open Matrix
open scoped Topology ContDiff Matrix ComplexOrder
noncomputable section
namespace Yau.NodeProofs.E02Aux
open Yau

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- An explicit normal form for the computed Levi entries of a real
Hessian, allowing real coordinates of odd space-time dimension. -/
def realTensorLevi (A : E →L[ℝ] E →L[ℝ] ℝ) (R J : ι → E) : Matrix ι ι ℂ :=
  fun i j => ⟨(A (R j) (R i)+A (J j) (J i))/4,
    (A (R j) (J i)-A (J j) (R i))/4⟩

theorem realTensorLevi_sub_smul (A B : E →L[ℝ] E →L[ℝ] ℝ)
    (R J : ι → E) (c : ℝ) :
    realTensorLevi (A-c • B) R J = realTensorLevi A R J-(c : ℂ) • realTensorLevi B R J := by
  ext i j
  apply Complex.ext <;>
    simp only [realTensorLevi,_root_.sub_apply,_root_.smul_apply,smul_eq_mul,
      Matrix.sub_apply,Matrix.smul_apply,Complex.sub_re,Complex.sub_im,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im] <;> ring

/-- The normal form is exactly the original nested Wirtinger Levi
matrix of the genuinely C² function after the real affine pullback. -/
theorem leviMatrix_real_affine {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {f : E → ℝ} {z : F} (a : E) (L : F →L[ℝ] E)
    (hf : ContDiffAt ℝ 2 f (a+L z)) (dir : ι → F) :
    leviMatrix (fun y => f (a+L y)) z dir =
      realTensorLevi (fderiv ℝ (fderiv ℝ f) (a+L z))
        (fun i => L (dir i)) (fun i => L (Complex.I • dir i)) := by
  have hComp : ContDiffAt ℝ 2 (fun y => f (a+L y)) z :=
    hf.comp z (contDiff_const.add L.contDiff).contDiffAt
  have hPull := affinePullback_second_fderiv a L hf
  apply Matrix.ext
  intro i j
  apply Complex.ext
  · rw [(Yau.LeafProofs.L18Aux.leviMatrix_entry_re_im hComp dir i j).1,hPull]
    simp only [realTensorLevi,ContinuousLinearMap.bilinearComp_apply]
    ring
  · rw [(Yau.LeafProofs.L18Aux.leviMatrix_entry_re_im hComp dir i j).2,hPull]
    simp only [realTensorLevi,ContinuousLinearMap.bilinearComp_apply]
    ring

end Yau.NodeProofs.E02Aux
