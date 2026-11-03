import spec.CHAIN.CONTRACTS

/-! Actual spatial and temporal derivatives of a scalar function in a
fixed space-time chart, expressed by its real differential on the product. -/
noncomputable section
namespace Yau.NodeProofs.F01Aux
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem deriv_time_eq_product_fderiv (F : E × ℝ → ℂ) (x : E) (t : ℝ)
    (hF : DifferentiableAt ℝ F (x, t)) :
    deriv (fun s => F (x, s)) t = fderiv ℝ F (x, t) (0, 1) := by
  have hcurve : HasDerivAt (fun s : ℝ => (x, s)) (0, 1) t :=
    (hasDerivAt_const t x).prodMk (hasDerivAt_id t)
  exact (hF.hasFDerivAt.comp_hasDerivAt t hcurve).deriv

theorem fderiv_space_eq_product_fderiv (F : E × ℝ → ℂ) (x : E) (t : ℝ)
    (hF : DifferentiableAt ℝ F (x, t)) (v : E) :
    fderiv ℝ (fun y => F (y, t)) x v = fderiv ℝ F (x, t) (v, 0) := by
  have hcurve : HasFDerivAt (fun y : E => (y, t))
      ((ContinuousLinearMap.id ℝ E).prod (0 : E →L[ℝ] ℝ)) x :=
    (hasFDerivAt_id x).prodMk (hasFDerivAt_const t x)
  have hh := congrArg (fun L : E →L[ℝ] ℂ => L v)
    (hF.hasFDerivAt.comp x hcurve).fderiv
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.zero_apply] using hh

theorem product_directional_schwarz (F : E × ℝ → ℂ) (x : E) (t : ℝ)
    (hF : ContDiffAt ℝ 2 F (x, t)) (v : E) :
    fderiv ℝ (fun p => fderiv ℝ F p (0, 1)) (x, t) (v, 0) =
      fderiv ℝ (fun p => fderiv ℝ F p (v, 0)) (x, t) (0, 1) := by
  have hD := (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  rw [fderiv_clm_apply hD (differentiableAt_const (0, 1)),
    fderiv_clm_apply hD (differentiableAt_const (v, 0))]
  simpa using hF.isSymmSndFDerivAt (by norm_num) (v, 0) (0, 1)

end Yau.NodeProofs.F01Aux
