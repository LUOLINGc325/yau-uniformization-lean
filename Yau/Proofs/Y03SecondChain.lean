import Yau.Blueprint.Alignment

/-! The real second-order chain rule, derived from the actual Fréchet derivatives. -/

open scoped Topology
open Filter

noncomputable section

namespace Yau.Blueprint.Alignment.Y03Proof

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem hessian_apply_eq_fderiv_eval {f : E → F} {z : E}
    (hf : ContDiffAt ℝ 2 f z) (h v : E) :
    fderiv ℝ (fderiv ℝ f) z h v = fderiv ℝ (fun w => fderiv ℝ f w v) z h := by
  have hdf : DifferentiableAt ℝ (fderiv ℝ f) z :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  rw [fderiv_clm_apply hdf (differentiableAt_const v)]
  simp

theorem hessian_comp_apply {f : F → G} {γ : E → F} {z : E}
    (hf : ContDiffAt ℝ 2 f (γ z)) (hγ : ContDiffAt ℝ 2 γ z) (h v : E) :
    fderiv ℝ (fderiv ℝ (f ∘ γ)) z h v =
      fderiv ℝ f (γ z) (fderiv ℝ (fderiv ℝ γ) z h v) +
        fderiv ℝ (fderiv ℝ f) (γ z) (fderiv ℝ γ z h) (fderiv ℝ γ z v) := by
  have hγd : DifferentiableAt ℝ γ z := hγ.differentiableAt (by norm_num)
  have hdf : DifferentiableAt ℝ (fderiv ℝ f) (γ z) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hDγ : DifferentiableAt ℝ (fderiv ℝ γ) z :=
    (hγ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have heq : (fun w => fderiv ℝ (f ∘ γ) w v) =ᶠ[𝓝 z]
      fun w => fderiv ℝ f (γ w) (fderiv ℝ γ w v) := by
    filter_upwards [hγ.eventually (by norm_num), hγ.continuousAt (hf.eventually (by norm_num))]
      with w hγw hfw
    change ContDiffAt ℝ 2 f (γ w) at hfw
    rw [fderiv_comp w (hfw.differentiableAt (by norm_num)) (hγw.differentiableAt (by norm_num))]
    rfl
  rw [hessian_apply_eq_fderiv_eval (hf.comp z hγ), heq.fderiv_eq,
    fderiv_clm_apply (c := fun w => fderiv ℝ f (γ w))
      (hdf.comp z hγd) (hDγ.clm_apply (differentiableAt_const v)),
    fderiv_fun_comp z hdf hγd, fderiv_clm_apply hDγ (differentiableAt_const v)]
  simp

end Yau.Blueprint.Alignment.Y03Proof
