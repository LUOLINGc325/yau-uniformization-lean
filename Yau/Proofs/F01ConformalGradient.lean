import Yau.Proofs.F01ConformalDual
import Yau.Proofs.F01ConformalBounds

/-! The actual Wirtinger gradient of the explicit conformal factor. -/
noncomputable section
open scoped ContDiff
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}

theorem wirt_ofReal_scalar_comp {u : ComplexVector n → ℝ} {F : ℝ → ℝ}
    {z : ComplexVector n} {A : ℝ} (hu : DifferentiableAt ℝ u z)
    (hF : HasDerivAt F A (u z)) (v : ComplexVector n) :
    wirt (fun w => (F (u w) : ℂ)) z v =
      (A : ℂ) * wirt (fun w => (u w : ℂ)) z v := by
  have hreal := hF.hasFDerivAt.comp z hu.hasFDerivAt
  have hcomplex : fderiv ℝ (fun w => (F (u w) : ℂ)) z =
      Complex.ofRealCLM.comp (fderiv ℝ (F ∘ u) z) := by
    change fderiv ℝ (Complex.ofRealCLM ∘ (F ∘ u)) z = _
    rw [fderiv_comp z Complex.ofRealCLM.differentiableAt hreal.differentiableAt, ContinuousLinearMap.fderiv]
  have hucomplex : fderiv ℝ (fun w => (u w : ℂ)) z =
      Complex.ofRealCLM.comp (fderiv ℝ u z) := by
    change fderiv ℝ (Complex.ofRealCLM ∘ u) z = _
    rw [fderiv_comp z Complex.ofRealCLM.differentiableAt hu, ContinuousLinearMap.fderiv]
  simp only [wirt, hcomplex, hucomplex, ContinuousLinearMap.comp_apply,
    hreal.fderiv, ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul,
    Complex.ofRealCLM_apply, Complex.ofReal_mul]
  ring

theorem dualNormMat_real_smul_vector (H : Matrix (Fin n) (Fin n) ℂ)
    (a : ℝ) (ξ : ComplexVector n) :
    dualNormMat H ((a : ℂ) • ξ) = a ^ 2 * dualNormMat H ξ := by
  simp only [dualNormMat, WithLp.ofLp_smul, star_smul, Matrix.mulVec_smul,
    smul_dotProduct, dotProduct_smul, smul_eq_mul, Complex.star_def, Complex.conj_ofReal,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  ring

theorem conformalScalar_wirt (u : M.Carrier → ℝ) (hu : SmoothFn u)
    {L : ℝ} (hL : 0 < L) (x : M.Carrier) (hx : u x < L) (v : ComplexVector n) :
    wirt (fun z => Complex.ofReal (inChart x (conformalScalar u L) z)) (chartPt x x) v =
      ((deriv conformalProfile (u x / L) / L : ℝ) : ℂ) *
        wirt (fun z => Complex.ofReal (inChart x u z)) (chartPt x x) v := by
  have hux : inChart x u (chartPt x x) = u x := by simp [inChart, chartInv, chartPt]
  have hprof : DifferentiableAt ℝ conformalProfile (u x / L) :=
    (conformalProfile_contDiffOn.contDiffAt
      (isOpen_Iio.mem_nhds ((div_lt_one hL).mpr hx))).differentiableAt (by simp)
  have hF : HasDerivAt (fun s : ℝ => conformalProfile (s / L))
      (deriv conformalProfile (u x / L) / L) (u x) := by
    simpa only [Function.comp_def, id_eq, one_div, div_eq_mul_inv, one_mul] using
      hprof.hasDerivAt.comp (u x) ((hasDerivAt_id (u x)).div_const L)
  have hU : DifferentiableAt ℝ (inChart x u) (chartPt x x) :=
    ((hu x).contDiffAt ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds
      (mem_extChartAt_target x))).differentiableAt (by simp)
  have hF' : HasDerivAt (fun s : ℝ => conformalProfile (s / L))
      (deriv conformalProfile (u x / L) / L) (inChart x u (chartPt x x)) := by
    rw [hux]
    exact hF
  simpa only [inChart, conformalScalar] using wirt_ofReal_scalar_comp hU hF' v

end Yau.NodeProofs.F01Aux
