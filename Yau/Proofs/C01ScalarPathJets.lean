import Yau.Proofs.C01ScalarSpaceTime

/-! Real path derivatives in precisely the original complex Wirtinger
and real time conventions of the scalar differential Harnack inequality. -/

noncomputable section

open scoped Topology ContDiff Matrix

namespace Yau.NodeProofs.C01Aux

open Yau Yau.Blueprint

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem real_fderiv_eq_two_wirt_re {f : E → ℝ} {z : E}
    (hf : DifferentiableAt ℝ f z) (v : E) :
    fderiv ℝ f z v = 2 * (wirt (fun p => (f p : ℂ)) z v).re := by
  have hc := Complex.ofRealCLM.hasFDerivAt.comp z hf.hasFDerivAt
  change HasFDerivAt (fun p => (f p : ℂ))
    (Complex.ofRealCLM.comp (fderiv ℝ f z)) z at hc
  rw [wirt, hc.fderiv]
  simp only [ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply]
  norm_num [Complex.mul_re] <;> ring

theorem fderiv_product_spacetime_split {F : E × ℝ → ℝ} {z : E} {t : ℝ}
    (hF : DifferentiableAt ℝ F (z, t)) (v : E) (a : ℝ) :
    fderiv ℝ F (z, t) (v, a) =
      fderiv ℝ (fun p => F (p, t)) z v + a * deriv (fun s => F (z, s)) t := by
  have hγz : HasFDerivAt (fun p : E => (p, t))
      ((ContinuousLinearMap.id ℝ E).prod 0) z := by
    simpa only [id_eq] using! (hasFDerivAt_id z).prodMk (hasFDerivAt_const t z)
  have hz := hF.hasFDerivAt.comp z hγz
  have hspace : fderiv ℝ (fun p => F (p, t)) z v = fderiv ℝ F (z, t) (v, 0) := by
    have hdf := hz.fderiv
    simp only [Function.comp_def] at hdf
    rw [hdf]
    rfl
  have hγt : HasDerivAt (fun s : ℝ => (z, s)) ((0 : E), (1 : ℝ)) t := by
    simpa only [id_eq] using! (hasDerivAt_const t z).prodMk (hasDerivAt_id t)
  have htime : deriv (fun s => F (z, s)) t = fderiv ℝ F (z, t) (0, 1) := by
    simpa only [Function.comp_def] using (hF.hasFDerivAt.comp_hasDerivAt t hγt).deriv
  rw [hspace, htime]
  have hsplit : (v, a) = (v, (0 : ℝ)) + a • ((0 : E), (1 : ℝ)) := by
    ext <;> simp
  rw [hsplit, map_add, map_smul]
  rfl

theorem spacetime_curve_hasDerivAt
    {F : E × ℝ → ℝ} {z : ℝ → E} {τ : ℝ → ℝ} {s : ℝ} {v : E} {a : ℝ}
    (hF : DifferentiableAt ℝ F (z s, τ s)) (hz : HasDerivAt z v s)
    (hτ : HasDerivAt τ a s) :
    HasDerivAt (fun u => F (z u, τ u))
      (2 * (wirt (fun p => (F (p, τ s) : ℂ)) (z s) v).re +
        a * deriv (fun t => F (z s, t)) (τ s)) s := by
  have hc := hF.hasFDerivAt.comp_hasDerivAt s (hz.prodMk hτ)
  have hinner : DifferentiableAt ℝ (fun p : E => (p, τ s)) (z s) :=
    differentiableAt_id.prodMk (differentiableAt_const (τ s))
  have hspace : DifferentiableAt ℝ (fun p => F (p, τ s)) (z s) :=
    hF.comp (z s) hinner
  rw [fderiv_product_spacetime_split hF v a, real_fderiv_eq_two_wirt_re hspace v] at hc
  simpa only [Function.comp_def] using hc

end Yau.NodeProofs.C01Aux
