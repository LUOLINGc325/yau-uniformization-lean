import Yau.Proofs.C01AffineCotangentJets

/-! Exact first and second logarithmic-time Wirtinger derivatives.  The
clock is the original `t = exp(w + conjugate w)`, including its factor two. -/

noncomputable section

open scoped Topology ContDiff

namespace Yau.NodeProofs.C01Aux

open Yau

theorem logarithmic_time_hasFDerivAt (w ζ : ℂ) :
    HasFDerivAt (fun q : ℂ => Real.exp (2 * (w + q).re))
      ((2 * Real.exp (2 * (w + ζ).re)) • Complex.reCLM) ζ := by
  have hreal : HasFDerivAt (fun q : ℂ => (w + q).re) Complex.reCLM ζ := by
    simpa only [ContinuousLinearMap.comp_id, Function.comp_def, id_eq] using!
      Complex.reCLM.hasFDerivAt.comp ζ ((hasFDerivAt_id ζ).const_add w)
  convert (hreal.const_mul 2).exp using 1
  ext q
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem logarithmic_time_wirtinger
    (f : ℝ → ℂ) (w ζ : ℂ) (a : ℂ)
    (hf : HasDerivAt f a (Real.exp (2 * (w + ζ).re))) :
    wirt (fun q : ℂ => f (Real.exp (2 * (w + q).re))) ζ 1 =
        (Real.exp (2 * (w + ζ).re) : ℂ) * a ∧
      wirtBar (fun q : ℂ => f (Real.exp (2 * (w + q).re))) ζ 1 =
        (Real.exp (2 * (w + ζ).re) : ℂ) * a := by
  have hd := hf.hasFDerivAt.comp ζ (logarithmic_time_hasFDerivAt w ζ)
  have hdf := hd.fderiv
  simp only [Function.comp_def] at hdf
  constructor
  · unfold wirt
    rw [hdf]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
      ContinuousLinearMap.smul_apply, Complex.reCLM_apply, smul_eq_mul,
      Complex.one_re, Complex.I_re, mul_one, mul_zero, zero_smul,
      zero_mul, sub_zero, one_smul, Complex.real_smul, Complex.ofReal_mul]
    push_cast
    ring
  · unfold wirtBar
    rw [hdf]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
      ContinuousLinearMap.smul_apply, Complex.reCLM_apply, smul_eq_mul,
      Complex.one_re, Complex.I_re, mul_one, mul_zero, zero_smul,
      zero_mul, add_zero, one_smul, Complex.real_smul, Complex.ofReal_mul]
    push_cast
    ring

theorem logarithmic_time_mixed
    (f f₁ : ℝ → ℂ) (w ζ : ℂ) (a₂ : ℂ)
    (hf : ∀ t : ℝ, 0 < t → HasDerivAt f (f₁ t) t)
    (hf₁ : HasDerivAt f₁ a₂ (Real.exp (2 * (w + ζ).re))) :
    let t := Real.exp (2 * (w + ζ).re)
    wirt (fun p => wirtBar (fun q : ℂ =>
      f (Real.exp (2 * (w + q).re))) p 1) ζ 1 =
        (t : ℂ) * f₁ t + (t : ℂ) ^ 2 * a₂ := by
  dsimp only
  have hinner :
      (fun p => wirtBar (fun q : ℂ => f (Real.exp (2 * (w + q).re))) p 1) =
      (fun p : ℂ => (Real.exp (2 * (w + p).re) : ℂ) *
        f₁ (Real.exp (2 * (w + p).re))) := by
    funext p
    exact (logarithmic_time_wirtinger f w p _ (hf _ (Real.exp_pos _))).2
  rw [hinner]
  have hreal : HasDerivAt (fun t : ℝ => (t : ℂ)) 1
      (Real.exp (2 * (w + ζ).re)) := by
    simpa using! Complex.ofRealCLM.hasFDerivAt.hasDerivAt
  have hF := hreal.mul hf₁
  have hclock := (logarithmic_time_wirtinger
    (fun t : ℝ => (t : ℂ) * f₁ t) w ζ _ hF).1
  convert hclock using 1 <;> ring

end Yau.NodeProofs.C01Aux
