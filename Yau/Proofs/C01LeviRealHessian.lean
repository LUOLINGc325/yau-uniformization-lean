import Yau.Proofs.C01AffineCotangentJets

/-! Exact real Hessian coordinates of the Levi operator for the original
scalar Harnack calculation.  The elementary complexification argument is
reproved from canonical L18 at A e0dbe0df without importing its cluster. -/

noncomputable section

open scoped Topology ContDiff Matrix
open Filter

namespace Yau.NodeProofs.C01Aux

open Yau
open Yau.Blueprint.Alignment.Y03Proof

theorem secondFDeriv_ofReal
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {z : E} (hf : ContDiffAt ℝ 2 f z) (v w : E) :
    fderiv ℝ (fderiv ℝ (fun y => (f y : ℂ))) z w v =
      (fderiv ℝ (fderiv ℝ f) z w v : ℂ) := by
  have hdf : DifferentiableAt ℝ (fderiv ℝ f) z :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hF : ContDiffAt ℝ 2 (fun y => (f y : ℂ)) z :=
    hf.continuousLinearMap_comp Complex.ofRealCLM
  have hdF : DifferentiableAt ℝ (fderiv ℝ (fun y => (f y : ℂ))) z :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have heq : (fun y => fderiv ℝ (fun y => (f y : ℂ)) y v) =ᶠ[𝓝 z]
      (fun y => (fderiv ℝ f y v : ℂ)) := by
    filter_upwards [hf.eventually (by norm_num)] with y hy
    have hd := hy.differentiableAt (by norm_num)
    change fderiv ℝ (Complex.ofRealCLM ∘ f) y v = _
    rw [fderiv_comp y Complex.ofRealCLM.differentiableAt hd]
    simp
  have h := congrArg (fun L : E →L[ℝ] ℂ => L w) heq.fderiv_eq
  rw [fderiv_clm_apply hdF (differentiableAt_const v)] at h
  change _ = fderiv ℝ (Complex.ofRealCLM ∘ (fun y => fderiv ℝ f y v)) z w at h
  rw [fderiv_comp z Complex.ofRealCLM.differentiableAt
    (hdf.clm_apply (differentiableAt_const v)),
    fderiv_clm_apply hdf (differentiableAt_const v)] at h
  simpa using h

theorem mixedLevi_eq_secondFDeriv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {F : E → ℂ} {z : E} (hF : ContDiffAt ℝ 2 F z) (v w : E) :
    wirt (fun y => wirtBar F y v) z w =
      (1 / 4 : ℂ) * (fderiv ℝ (fderiv ℝ F) z w v +
        fderiv ℝ (fderiv ℝ F) z (Complex.I • w) (Complex.I • v) +
        Complex.I * (fderiv ℝ (fderiv ℝ F) z w (Complex.I • v) -
          fderiv ℝ (fderiv ℝ F) z (Complex.I • w) v)) := by
  rw [wirt, fderiv_wirtBar_apply hF, fderiv_wirtBar_apply hF]
  linear_combination -(1 / 4 : ℂ) *
    fderiv ℝ (fderiv ℝ F) z (Complex.I • w) (Complex.I • v) * Complex.I_sq

/-- Both real Hessian directions are retained, including unequal ones. -/
theorem mixedLevi_real_parts
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : E → ℝ} {z : E} (hf : ContDiffAt ℝ 2 f z) (v w : E) :
    (wirt (fun y => wirtBar (fun q => (f q : ℂ)) y v) z w).re =
      (1 / 4 : ℝ) * (fderiv ℝ (fderiv ℝ f) z w v +
        fderiv ℝ (fderiv ℝ f) z (Complex.I • w) (Complex.I • v)) ∧
    (wirt (fun y => wirtBar (fun q => (f q : ℂ)) y v) z w).im =
      (1 / 4 : ℝ) * (fderiv ℝ (fderiv ℝ f) z w (Complex.I • v) -
        fderiv ℝ (fderiv ℝ f) z (Complex.I • w) v) := by
  have hF : ContDiffAt ℝ 2 (fun y => (f y : ℂ)) z :=
    hf.continuousLinearMap_comp Complex.ofRealCLM
  rw [mixedLevi_eq_secondFDeriv hF]
  simp only [secondFDeriv_ofReal hf]
  constructor <;> simp [Complex.mul_re, Complex.mul_im]

theorem mixedLevi_re_swap
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : E → ℝ} {z : E} (hf : ContDiffAt ℝ 2 f z) (v w : E) :
    (wirt (fun y => wirtBar (fun q => (f q : ℂ)) y v) z w).re =
      (wirt (fun y => wirtBar (fun q => (f q : ℂ)) y w) z v).re := by
  rw [(mixedLevi_real_parts hf v w).1, (mixedLevi_real_parts hf w v).1,
    (hf.isSymmSndFDerivAt (by norm_num)).eq w v,
    (hf.isSymmSndFDerivAt (by norm_num)).eq (Complex.I • w) (Complex.I • v)]

end Yau.NodeProofs.C01Aux
