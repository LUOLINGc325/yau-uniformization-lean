import Yau.Proofs.V03LeviChain

/-! V01 scratch source. The real quadratic tensor is converted to the
paper-convention Levi matrix using the published V03 Wirtinger computation. -/

noncomputable section
open scoped Topology ContDiff Matrix

namespace Yau.Blueprint.V01Proof

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def realHessianLevi (A : E →L[ℝ] E →L[ℝ] ℝ) (dir : ι → E) : Matrix ι ι ℂ :=
  fun i j => (1 / 4 : ℂ) *
    ((A (dir j) (dir i) : ℂ) +
      (A (Complex.I • dir j) (Complex.I • dir i) : ℂ) +
      Complex.I * ((A (dir j) (Complex.I • dir i) : ℂ) -
        (A (Complex.I • dir j) (dir i) : ℂ)))

theorem leviMatrix_eq_realHessianLevi {f : E → ℝ} {z : E}
    (hf : ContDiffAt ℝ 2 f z) (dir : ι → E) :
    leviMatrix f z dir = realHessianLevi (fderiv ℝ (fderiv ℝ f) z) dir := by
  have hF : ContDiffAt ℝ 2 (fun y => (f y : ℂ)) z :=
    hf.continuousLinearMap_comp Complex.ofRealCLM
  have hd := (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  ext i j
  change wirt (fun y => wirtBar (fun u => (f u : ℂ)) y (dir i)) z (dir j) = _
  rw [Yau.Blueprint.V03Proof.mixedWirt_eq_secondFDeriv hd]
  simp only [Yau.Blueprint.V03Proof.secondFDeriv_ofReal hf]
  rfl

theorem realHessianLevi_sub (A B : E →L[ℝ] E →L[ℝ] ℝ) (dir : ι → E) :
    realHessianLevi (A - B) dir = realHessianLevi A dir - realHessianLevi B dir := by
  ext i j
  simp only [realHessianLevi, ContinuousLinearMap.sub_apply, Complex.ofReal_sub,
    Matrix.sub_apply]
  ring

theorem realHessianLevi_real_smul (a : ℝ) (A : E →L[ℝ] E →L[ℝ] ℝ)
    (dir : ι → E) :
    realHessianLevi (a • A) dir = (a : ℂ) • realHessianLevi A dir := by
  ext i j
  simp only [realHessianLevi, ContinuousLinearMap.smul_apply, smul_eq_mul,
    Complex.ofReal_mul, Matrix.smul_apply]
  ring

theorem leviMatrix_eq_of_secondFDeriv_eq {f g : E → ℝ} {x y : E}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g y)
    (hjet : fderiv ℝ (fderiv ℝ f) x = fderiv ℝ (fderiv ℝ g) y) (dir : ι → E) :
    leviMatrix f x dir = leviMatrix g y dir := by
  rw [leviMatrix_eq_realHessianLevi hf, leviMatrix_eq_realHessianLevi hg, hjet]

end Yau.Blueprint.V01Proof
