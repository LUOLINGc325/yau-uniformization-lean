import Yau.Proofs.V03LeviMatrix

/-! Linearity of the actual Levi matrix, with genuine C² hypotheses for
both nested derivatives. -/

open scoped Topology ContDiff Matrix
open Filter

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem mixedWirt_add {f g : E → ℂ} {z : E}
    (hf : ContDiffAt ℝ 2 f z) (hg : ContDiffAt ℝ 2 g z) (v w : E) :
    wirt (fun y => wirtBar (fun x => f x + g x) y v) z w =
      wirt (fun y => wirtBar f y v) z w + wirt (fun y => wirtBar g y v) z w := by
  have heq : (fun y => wirtBar (fun x => f x + g x) y v) =ᶠ[𝓝 z]
      (fun y => wirtBar f y v + wirtBar g y v) := by
    filter_upwards [hf.eventually (by norm_num), hg.eventually (by norm_num)] with y hfy hgy
    exact wirtBar_add f g y v (hfy.differentiableAt (by norm_num)) (hgy.differentiableAt (by norm_num))
  have hw : wirt (fun y => wirtBar (fun x => f x + g x) y v) z w =
      wirt (fun y => wirtBar f y v + wirtBar g y v) z w := by
    unfold wirt
    rw [heq.fderiv_eq]
  rw [hw, wirt_add _ _ z w (wirtBar_differentiableAt hf v) (wirtBar_differentiableAt hg v)]

theorem mixedWirt_const_mul {f : E → ℂ} {z : E}
    (hf : ContDiffAt ℝ 2 f z) (c : ℂ) (v w : E) :
    wirt (fun y => wirtBar (fun x => c * f x) y v) z w =
      c * wirt (fun y => wirtBar f y v) z w := by
  have heq : (fun y => wirtBar (fun x => c * f x) y v) =ᶠ[𝓝 z]
      (fun y => c * wirtBar f y v) := by
    filter_upwards [hf.eventually (by norm_num)] with y hy
    simp only [wirtBar, fderiv_const_mul (hy.differentiableAt (by norm_num)),
      ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  unfold wirt
  rw [heq.fderiv_eq]
  simp only [fderiv_const_mul (wirtBar_differentiableAt hf v),
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem leviMatrix_add {f g : E → ℝ} {z : E}
    (hf : ContDiffAt ℝ 2 f z) (hg : ContDiffAt ℝ 2 g z) (dir : ι → E) :
    leviMatrix (fun y => f y + g y) z dir = leviMatrix f z dir + leviMatrix g z dir := by
  ext a b
  simp only [leviMatrix, Complex.ofReal_add, Matrix.add_apply]
  exact mixedWirt_add (hf.continuousLinearMap_comp Complex.ofRealCLM)
    (hg.continuousLinearMap_comp Complex.ofRealCLM) (dir a) (dir b)

theorem leviMatrix_const_mul {f : E → ℝ} {z : E} (hf : ContDiffAt ℝ 2 f z)
    (c : ℝ) (dir : ι → E) :
    leviMatrix (fun y => c * f y) z dir = (c : ℂ) • leviMatrix f z dir := by
  ext a b
  simp only [leviMatrix, Complex.ofReal_mul, Matrix.smul_apply, smul_eq_mul]
  exact mixedWirt_const_mul (hf.continuousLinearMap_comp Complex.ofRealCLM)
    (c : ℂ) (dir a) (dir b)

end Yau.Blueprint.V03Proof
