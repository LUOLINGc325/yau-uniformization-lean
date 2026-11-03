import Yau.Proofs.V03LeviChain

/-! Real parts of holomorphic functions and logarithmic moduli of
nonvanishing holomorphic functions have zero actual diagonal Levi value. -/

open scoped Topology ContDiff
open Filter

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem secondFDeriv_re {f : E → ℂ} {z : E} (hf : ContDiffAt ℝ 2 f z) (v w : E) :
    fderiv ℝ (fderiv ℝ (fun y => (f y).re)) z v w =
      (fderiv ℝ (fderiv ℝ f) z v w).re := by
  have h := congrArg (fun A => A ![v, w])
    (Complex.reCLM.iteratedFDeriv_comp_left hf (by norm_num))
  simpa only [Function.comp_def, Complex.reCLM_apply,
    ContinuousLinearMap.compContinuousMultilinearMap_coe,
    iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one] using h

theorem mixedWirt_re_holomorphic_zero {f : E → ℂ} {z : E}
    (hf : ContDiffAt ℂ 2 f z) (v : E) :
    (wirt (fun y => wirtBar (fun y' => ((f y').re : ℂ)) y v) z v).re = 0 := by
  have hfr := hf.restrict_scalars ℝ
  have hre : ContDiffAt ℝ 2 (fun y => (f y).re) z :=
    hfr.continuousLinearMap_comp Complex.reCLM
  rw [mixedWirt_real_diagonal hre, secondFDeriv_re hfr, secondFDeriv_re hfr,
    secondFDeriv_complex_I_I hf]
  simp

theorem secondFDeriv_const_mul {f : E → ℝ} {z : E}
    (hf : ContDiffAt ℝ 2 f z) (c : ℝ) (v w : E) :
    fderiv ℝ (fderiv ℝ (fun y => c * f y)) z v w =
      c * fderiv ℝ (fderiv ℝ f) z v w := by
  have h := congrArg (fun A => A ![v, w]) (iteratedFDeriv_const_smul_apply (a := c) hf)
  simpa only [Pi.smul_def, iteratedFDeriv_two_apply, smul_apply,
    Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one] using h

theorem mixedWirt_real_const_mul {f : E → ℝ} {z : E}
    (hf : ContDiffAt ℝ 2 f z) (c : ℝ) (v : E) :
    (wirt (fun y => wirtBar (fun y' => ((c * f y' : ℝ) : ℂ)) y v) z v).re =
      c * (wirt (fun y => wirtBar (fun y' => (f y' : ℂ)) y v) z v).re := by
  rw [mixedWirt_real_diagonal (contDiffAt_const.mul hf), mixedWirt_real_diagonal hf]
  simp only [secondFDeriv_const_mul hf]
  ring

theorem mixedWirt_log_normSq_holomorphic_zero {f : E → ℂ} {z : E}
    (hf : ContDiffAt ℂ 2 f z) (hne : f z ≠ 0) (v : E) :
    (wirt (fun y => wirtBar (fun y' => (Real.log (Complex.normSq (f y')) : ℂ)) y v)
      z v).re = 0 := by
  let q : E → ℂ := fun y => f y / f z
  have hq : ContDiffAt ℂ 2 q z := hf.div_const _
  have hqz : q z = 1 := div_self hne
  have hlog : ContDiffAt ℂ 2 (fun y => Complex.log (q y)) z :=
    (Complex.contDiffAt_log (by rw [hqz]; exact Complex.one_mem_slitPlane)).comp z hq
  have hre : ContDiffAt ℝ 2 (fun y => (Complex.log (q y)).re) z :=
    (hlog.restrict_scalars ℝ).continuousLinearMap_comp Complex.reCLM
  have heq : (fun y => Real.log (Complex.normSq (f y))) =ᶠ[𝓝 z]
      (fun y => 2 * (Complex.log (q y)).re + Real.log (Complex.normSq (f z))) := by
    filter_upwards [hf.continuousAt.eventually_ne hne] with y hy
    simp only [Complex.normSq_eq_norm_sq, Real.log_pow, Complex.log_re, q, norm_div,
      Real.log_div (norm_ne_zero_iff.mpr hy) (norm_ne_zero_iff.mpr hne)]
    ring
  have heqC : (fun y => (Real.log (Complex.normSq (f y)) : ℂ)) =ᶠ[𝓝 z]
      (fun y => ((2 * (Complex.log (q y)).re : ℝ) : ℂ) +
        (Real.log (Complex.normSq (f z)) : ℂ)) :=
    heq.mono fun y hy => by
      simpa only [Complex.ofReal_add] using congrArg Complex.ofReal hy
  rw [mixedWirt_congr heqC, mixedWirt_add_const,
    mixedWirt_real_const_mul hre, mixedWirt_re_holomorphic_zero hlog, mul_zero]

end Yau.Blueprint.V03Proof
