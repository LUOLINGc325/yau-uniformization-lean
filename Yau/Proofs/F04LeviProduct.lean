import Yau.Proofs.F04Source
import Yau.Proofs.F04CovectorMatrix

open Filter Set
open scoped Topology ContDiff Matrix ComplexOrder

noncomputable section

namespace Yau.F04Proof

open Yau.LeafProofs.L14Aux

theorem wirt_add_at {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (f g : V → ℂ) (z v : V) (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    wirt (fun y => f y + g y) z v = wirt f z v + wirt g z v := by
  unfold wirt
  rw [fderiv_fun_add hf hg]
  simp only [add_apply]
  ring

theorem wirtBar_differentiableAt {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {f : V → ℂ} {z : V} (hf : ContDiffAt ℝ 2 f z) (v : V) :
    DifferentiableAt ℝ (fun y => wirtBar f y v) z := by
  have hD := (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  exact differentiableAt_const _ |>.mul
    ((hD.clm_apply (differentiableAt_const v)).add
      ((differentiableAt_const Complex.I).mul (hD.clm_apply (differentiableAt_const (Complex.I • v)))))

theorem wirtBar_ofReal_eq_star {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (f : V → ℝ) (z v : V) :
    wirtBar (fun y => (f y : ℂ)) z v = star (wirt (fun y => (f y : ℂ)) z v) := by
  simpa only [Complex.star_def, Complex.conj_ofReal] using wirtBar_star (fun y => (f y : ℂ)) z v

def complexGradient {n : ℕ} (f : ComplexVector n → ℝ) (z : ComplexVector n) : Fin n → ℂ :=
  fun i => wirt (fun y => (f y : ℂ)) z (stdVec i)

theorem leviC_mul {n : ℕ} {f g : ComplexVector n → ℝ} {z : ComplexVector n}
    (hf : ContDiffAt ℝ 2 f z) (hg : ContDiffAt ℝ 2 g z) :
    leviC (fun y => f y * g y) z =
      (g z : ℂ) • leviC f z + (f z : ℂ) • leviC g z +
        Matrix.vecMulVec (star (complexGradient f z)) (complexGradient g z) +
        Matrix.vecMulVec (star (complexGradient g z)) (complexGradient f z) := by
  let F : ComplexVector n → ℂ := fun y => (f y : ℂ)
  let G : ComplexVector n → ℂ := fun y => (g y : ℂ)
  have hF : ContDiffAt ℝ 2 F z := Complex.ofRealCLM.contDiff.contDiffAt.comp z hf
  have hG : ContDiffAt ℝ 2 G z := Complex.ofRealCLM.contDiff.contDiffAt.comp z hg
  have hFd := hF.differentiableAt (by norm_num)
  have hGd := hG.differentiableAt (by norm_num)
  ext i j
  have hinner :
      (fun y => wirtBar (fun v => ((f v * g v : ℝ) : ℂ)) y (stdVec i)) =ᶠ[𝓝 z]
        (fun y => wirtBar F y (stdVec i) * G y + F y * wirtBar G y (stdVec i)) := by
    filter_upwards [hF.eventually (by norm_num), hG.eventually (by norm_num)] with y hyF hyG
    simpa only [F, G, Complex.ofReal_mul] using wirtBar_mul_rule F G y (stdVec i)
      (hyF.differentiableAt (by norm_num)) (hyG.differentiableAt (by norm_num))
  have houter := congrArg (fun L : ComplexVector n →L[ℝ] ℂ =>
    (1 / 2 : ℂ) * (L (stdVec j) - Complex.I * L (Complex.I • stdVec j))) hinner.fderiv_eq
  change wirt (fun y => wirtBar (fun v => ((f v * g v : ℝ) : ℂ)) y (stdVec i)) z (stdVec j) = _
  change wirt (fun y => wirtBar (fun v => ((f v * g v : ℝ) : ℂ)) y (stdVec i)) z (stdVec j) =
    wirt (fun y => wirtBar F y (stdVec i) * G y + F y * wirtBar G y (stdVec i)) z (stdVec j) at houter
  rw [houter, wirt_add_at (fun y => wirtBar F y (stdVec i) * G y)
    (fun y => F y * wirtBar G y (stdVec i)) z (stdVec j)
    ((wirtBar_differentiableAt hF _).mul hGd) (hFd.mul (wirtBar_differentiableAt hG _)),
    wirt_mul_rule (fun y => wirtBar F y (stdVec i)) G z (stdVec j)
      (wirtBar_differentiableAt hF _) hGd,
    wirt_mul_rule F (fun y => wirtBar G y (stdVec i)) z (stdVec j)
      hFd (wirtBar_differentiableAt hG _)]
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.star_apply, smul_eq_mul]
  dsimp only [leviC, leviMatrix, complexGradient, F, G]
  rw [wirtBar_ofReal_eq_star f z (stdVec i), wirtBar_ofReal_eq_star g z (stdVec i)]
  ring

end Yau.F04Proof
