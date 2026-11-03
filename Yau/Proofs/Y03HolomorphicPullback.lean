import Yau.Proofs.Y03Levi
import Yau.Proofs.Y03SecondChain

/-! The Levi derivative pulls back along the actual nonlinear holomorphic curve. -/

open scoped Topology
open Filter

noncomputable section

namespace Yau.Blueprint.Alignment.Y03Proof

open Yau

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

theorem real_hessian_holomorphic_eval {γ : V → W} {z : V}
    (hγ : ContDiffAt ℂ 2 γ z) (v w : V) :
    fderiv ℝ (fderiv ℝ γ) z v w =
      fderiv ℂ (fun x => fderiv ℂ γ x w) z v := by
  have hD : DifferentiableAt ℂ (fderiv ℂ γ) z :=
    (hγ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hEval : DifferentiableAt ℂ (fun x => fderiv ℂ γ x w) z :=
    hD.clm_apply (differentiableAt_const w)
  have heq : (fun x => fderiv ℝ γ x w) =ᶠ[𝓝 z] fun x => fderiv ℂ γ x w := by
    filter_upwards [hγ.eventually (by norm_num)] with x hx
    rw [(hx.differentiableAt (by norm_num)).fderiv_restrictScalars ℝ]
    rfl
  rw [hessian_apply_eq_fderiv_eval (hγ.restrict_scalars ℝ), heq.fderiv_eq,
    hEval.fderiv_restrictScalars ℝ]
  rfl

theorem real_hessian_holomorphic_I_left {γ : V → W} {z : V}
    (hγ : ContDiffAt ℂ 2 γ z) (v w : V) :
    fderiv ℝ (fderiv ℝ γ) z (Complex.I • v) w =
      Complex.I • fderiv ℝ (fderiv ℝ γ) z v w := by
  rw [real_hessian_holomorphic_eval hγ, real_hessian_holomorphic_eval hγ, map_smul]

theorem real_hessian_holomorphic_I_I {γ : V → W} {z : V}
    (hγ : ContDiffAt ℂ 2 γ z) (v : V) :
    fderiv ℝ (fderiv ℝ γ) z (Complex.I • v) (Complex.I • v) =
      -fderiv ℝ (fderiv ℝ γ) z v v := by
  have hsym := ((hγ.restrict_scalars ℝ).isSymmSndFDerivAt (by norm_num)).eq v (Complex.I • v)
  rw [real_hessian_holomorphic_I_left hγ, hsym, real_hessian_holomorphic_I_left hγ]
  simp only [smul_smul, Complex.I_mul_I, neg_one_smul]

theorem levi_direction_comp_holomorphic {f : W → ℂ} {γ : V → W} {z : V}
    (hf : ContDiffAt ℝ 2 f (γ z)) (hγ : ContDiffAt ℂ 2 γ z) (v : V) :
    wirt (fun x => wirtBar (f ∘ γ) x v) z v =
      wirt (fun x => wirtBar f x (fderiv ℂ γ z v)) (γ z) (fderiv ℂ γ z v) := by
  have hγr : ContDiffAt ℝ 2 γ z := hγ.restrict_scalars ℝ
  have hd : ∀ w, fderiv ℝ γ z w = fderiv ℂ γ z w := by
    intro w
    rw [(hγ.differentiableAt (by norm_num)).fderiv_restrictScalars ℝ]
    rfl
  rw [levi_direction_eq_hessian (hf.comp z hγr), levi_direction_eq_hessian hf,
    hessian_comp_apply hf hγr, hessian_comp_apply hf hγr,
    real_hessian_holomorphic_I_I hγ]
  simp only [hd, map_smul, map_neg]
  ring

end Yau.Blueprint.Alignment.Y03Proof
