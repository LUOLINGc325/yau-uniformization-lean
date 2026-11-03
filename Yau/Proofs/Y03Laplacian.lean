import Yau.Proofs.Y03Levi
import Yau.Proofs.Y03SecondChain
import Yau.Proofs.Y03Maximum

/-! The strip's real Laplacian is four times the literal one-dimensional Levi form. -/

noncomputable section

namespace Yau.Blueprint.Alignment.Y03Proof

open Yau

theorem hessian_clm_comp {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : E → F} {z : E} (hf : ContDiffAt ℝ 2 f z) (L : F →L[ℝ] G) (h v : E) :
    fderiv ℝ (fderiv ℝ (L ∘ f)) z h v = L (fderiv ℝ (fderiv ℝ f) z h v) := by
  have hDL : fderiv ℝ (fderiv ℝ (L : F → G)) (f z) = 0 := by
    have heq : fderiv ℝ (L : F → G) = fun _ => L := funext fun x => L.fderiv
    rw [heq]
    simp
  have hc := hessian_comp_apply (f := L) (γ := f) L.contDiff.contDiffAt hf h v
  rw [L.fderiv, hDL] at hc
  simpa using hc

theorem secondDeriv_affine_comp {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {z₀ v : E} {x : ℝ} (hf : ContDiffAt ℝ 2 f (z₀ + x • v)) :
    deriv (deriv (fun t : ℝ => f (z₀ + t • v))) x =
      fderiv ℝ (fderiv ℝ f) (z₀ + x • v) v v := by
  let L : ℝ →L[ℝ] E := ContinuousLinearMap.toSpanSingleton ℝ v
  have hγ : ContDiffAt ℝ 2 (fun t => z₀ + L t) x := by fun_prop
  have hfg : ContDiffAt ℝ 2 (fun t : ℝ => f (z₀ + t • v)) x := hf.comp x hγ
  have heval : fderiv ℝ (fderiv ℝ (fun t : ℝ => f (z₀ + t • v))) x 1 1 =
      deriv (deriv (fun t : ℝ => f (z₀ + t • v))) x := by
    rw [hessian_apply_eq_fderiv_eval hfg]
    rfl
  have hc := hessian_comp_apply (γ := fun t => z₀ + L t) hf hγ (1 : ℝ) (1 : ℝ)
  change fderiv ℝ (fderiv ℝ (fun t : ℝ => f (z₀ + t • v))) x 1 1 = _ at hc
  rw [heval] at hc
  have hDγ : fderiv ℝ (fun t => z₀ + L t) = fun _ => L := by
    funext t
    rw [fderiv_const_add, L.fderiv]
  simp only [hDγ, fderiv_fun_const] at hc
  simpa [L] using hc

theorem axisLaplacian_complex_coordinates {f : ℂ → ℝ} {z : ℝ × ℝ}
    (hf : ContDiffAt ℝ 2 f (Complex.equivRealProdCLM.symm z)) :
    axisLaplacian (f ∘ Complex.equivRealProdCLM.symm) z =
      fderiv ℝ (fderiv ℝ f) (Complex.equivRealProdCLM.symm z) 1 1 +
        fderiv ℝ (fderiv ℝ f) (Complex.equivRealProdCLM.symm z) Complex.I Complex.I := by
  have hz : Complex.equivRealProdCLM.symm z = (z.2 : ℂ) * Complex.I + z.1 • (1 : ℂ) := by
    rw [Complex.equivRealProdCLM_symm_apply, Complex.real_smul]
    ring
  have hz' : Complex.equivRealProdCLM.symm z = (z.1 : ℂ) + z.2 • Complex.I := by
    rw [Complex.equivRealProdCLM_symm_apply, Complex.real_smul]
  have hx : (fun t : ℝ => (f ∘ Complex.equivRealProdCLM.symm) (t, z.2)) =
      fun t => f ((z.2 : ℂ) * Complex.I + t • (1 : ℂ)) := by
    funext t
    simp only [Function.comp_apply, Complex.equivRealProdCLM_symm_apply, Complex.real_smul]
    congr 1
    ring
  have hy : (fun t : ℝ => (f ∘ Complex.equivRealProdCLM.symm) (z.1, t)) =
      fun t => f ((z.1 : ℂ) + t • Complex.I) := by
    funext t
    simp only [Function.comp_apply, Complex.equivRealProdCLM_symm_apply, Complex.real_smul]
  unfold axisLaplacian
  rw [hx, hy, secondDeriv_affine_comp (hz ▸ hf), secondDeriv_affine_comp (hz' ▸ hf),
    ← hz, ← hz']

theorem axisLaplacian_eq_four_re_levi {f : ℂ → ℝ} {z : ℝ × ℝ}
    (hf : ContDiffAt ℝ 2 f (Complex.equivRealProdCLM.symm z)) :
    axisLaplacian (f ∘ Complex.equivRealProdCLM.symm) z =
      4 * (wirt (fun w => wirtBar (fun u => (f u : ℂ)) w 1)
        (Complex.equivRealProdCLM.symm z) 1).re := by
  have hfc : ContDiffAt ℝ 2 (Complex.ofRealCLM ∘ f) (Complex.equivRealProdCLM.symm z) :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp _ hf
  change _ = 4 * (wirt (fun w => wirtBar (Complex.ofRealCLM ∘ f) w 1)
    (Complex.equivRealProdCLM.symm z) 1).re
  rw [axisLaplacian_complex_coordinates hf,
    levi_direction_eq_hessian (f := Complex.ofRealCLM ∘ f) hfc]
  rw [hessian_clm_comp hf Complex.ofRealCLM, hessian_clm_comp hf Complex.ofRealCLM]
  simp only [smul_eq_mul, mul_one, Complex.ofRealCLM_apply, Complex.mul_re, Complex.add_re,
    Complex.ofReal_re]
  norm_num
  ring

end Yau.Blueprint.Alignment.Y03Proof
