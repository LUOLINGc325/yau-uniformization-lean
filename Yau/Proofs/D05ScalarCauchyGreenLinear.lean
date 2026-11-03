import Yau.Proofs.D05ScalarCauchyGreen

/-! Linearity of the same compact-density Cauchy–Green construction.
In particular antisymmetric coefficients retain antisymmetric solutions. -/

open scoped Topology ContDiff
open MeasureTheory

noncomputable section
namespace Yau.Blueprint.D05Proof
open Yau Yau.LeafProofs

theorem compactNewtonPotential_add {f g : ℂ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hsf : HasCompactSupport f)
    (hg : ContDiff ℝ ∞ g) (hsg : HasCompactSupport g) (z : ℂ) :
    compactNewtonPotential (fun w => f w + g w) z =
      compactNewtonPotential f z + compactNewtonPotential g z := by
  unfold compactNewtonPotential
  simp_rw [mul_add]
  exact integral_add (L08_integrable_logPotential_compact hf hsf z)
    (L08_integrable_logPotential_compact hg hsg z)

theorem compactNewtonPotential_real_mul (f : ℂ → ℝ) (a : ℝ) (z : ℂ) :
    compactNewtonPotential (fun w => a * f w) z = a * compactNewtonPotential f z := by
  unfold compactNewtonPotential
  simp_rw [mul_left_comm _ a]
  exact integral_const_mul _ _

theorem compactDbarRealSolution_add {f g : ℂ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hsf : HasCompactSupport f)
    (hg : ContDiff ℝ ∞ g) (hsg : HasCompactSupport g) :
    compactDbarRealSolution (fun w => f w + g w) =
      fun z => compactDbarRealSolution f z + compactDbarRealSolution g z := by
  have hPF : ContDiff ℝ ∞ (fun z => (compactNewtonPotential f z : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (L08_contDiff_logPotential_compact hf hsf)
  have hPG : ContDiff ℝ ∞ (fun z => (compactNewtonPotential g z : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (L08_contDiff_logPotential_compact hg hsg)
  have hP : (fun z => (compactNewtonPotential (fun w => f w + g w) z : ℂ)) =
      fun z => (compactNewtonPotential f z : ℂ) + (compactNewtonPotential g z : ℂ) := by
    funext z
    rw [compactNewtonPotential_add hf hsf hg hsg, Complex.ofReal_add]
  funext z
  simp only [compactDbarRealSolution, hP]
  rw [V03Proof.wirt_add _ _ z 1 (hPF.contDiffAt.differentiableAt (by simp))
    (hPG.contDiffAt.differentiableAt (by simp))]
  ring

theorem compactDbarRealSolution_real_mul {f : ℂ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hsf : HasCompactSupport f) (a : ℝ) :
    compactDbarRealSolution (fun w => a * f w) =
      fun z => (a : ℂ) * compactDbarRealSolution f z := by
  have hPF : ContDiff ℝ ∞ (fun z => (compactNewtonPotential f z : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (L08_contDiff_logPotential_compact hf hsf)
  have hP : (fun z => (compactNewtonPotential (fun w => a * f w) z : ℂ)) =
      fun z => (a : ℂ) * (compactNewtonPotential f z : ℂ) := by
    funext z
    rw [compactNewtonPotential_real_mul, Complex.ofReal_mul]
  funext z
  simp only [compactDbarRealSolution, hP, wirt,
    fderiv_const_mul (hPF.contDiffAt.differentiableAt (by simp)), smul_apply, smul_eq_mul]
  ring

theorem compactDbarRealSolution_neg {f : ℂ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hsf : HasCompactSupport f) :
    compactDbarRealSolution (fun w => -f w) = fun z => -compactDbarRealSolution f z := by
  simpa using compactDbarRealSolution_real_mul hf hsf (-1)

theorem compactDbarSolution_add {b c : ℂ → ℂ}
    (hb : ContDiff ℝ ∞ b) (hsb : HasCompactSupport b)
    (hc : ContDiff ℝ ∞ c) (hsc : HasCompactSupport c) :
    compactDbarSolution (fun w => b w + c w) =
      fun z => compactDbarSolution b z + compactDbarSolution c z := by
  have hbre : ContDiff ℝ ∞ (fun w => (b w).re) := Complex.reCLM.contDiff.comp hb
  have hbim : ContDiff ℝ ∞ (fun w => (b w).im) := Complex.imCLM.contDiff.comp hb
  have hcre : ContDiff ℝ ∞ (fun w => (c w).re) := Complex.reCLM.contDiff.comp hc
  have hcim : ContDiff ℝ ∞ (fun w => (c w).im) := Complex.imCLM.contDiff.comp hc
  funext z
  simp only [compactDbarSolution, Complex.add_re, Complex.add_im,
    compactDbarRealSolution_add hbre (hsb.comp_left (by simp)) hcre (hsc.comp_left (by simp)),
    compactDbarRealSolution_add hbim (hsb.comp_left (by simp)) hcim (hsc.comp_left (by simp))]
  ring

theorem compactDbarSolution_real_mul {b : ℂ → ℂ}
    (hb : ContDiff ℝ ∞ b) (hsb : HasCompactSupport b) (a : ℝ) :
    compactDbarSolution (fun w => (a : ℂ) * b w) =
      fun z => (a : ℂ) * compactDbarSolution b z := by
  have hbre : ContDiff ℝ ∞ (fun w => (b w).re) := Complex.reCLM.contDiff.comp hb
  have hbim : ContDiff ℝ ∞ (fun w => (b w).im) := Complex.imCLM.contDiff.comp hb
  funext z
  simp only [compactDbarSolution, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, sub_zero,
    compactDbarRealSolution_real_mul hbre (hsb.comp_left (by simp)),
    compactDbarRealSolution_real_mul hbim (hsb.comp_left (by simp))]
  ring

theorem compactDbarSolution_I_mul {b : ℂ → ℂ}
    (hb : ContDiff ℝ ∞ b) (hsb : HasCompactSupport b) :
    compactDbarSolution (fun w => Complex.I * b w) =
      fun z => Complex.I * compactDbarSolution b z := by
  have hbim : ContDiff ℝ ∞ (fun w => (b w).im) := Complex.imCLM.contDiff.comp hb
  funext z
  simp only [compactDbarSolution, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub, zero_add,
    compactDbarRealSolution_neg hbim (hsb.comp_left (by simp))]
  linear_combination -compactDbarRealSolution (fun w => (b w).im) z * Complex.I_sq

theorem compactDbarSolution_const_mul {b : ℂ → ℂ}
    (hb : ContDiff ℝ ∞ b) (hsb : HasCompactSupport b) (a : ℂ) :
    compactDbarSolution (fun w => a * b w) =
      fun z => a * compactDbarSolution b z := by
  have hreal (r : ℝ) : ContDiff ℝ ∞ (fun w => (r : ℂ) * b w) :=
    contDiff_const.mul hb
  have hsreal (r : ℝ) : HasCompactSupport (fun w => (r : ℂ) * b w) :=
    hsb.comp_left (by simp)
  have heq : (fun w => a * b w) =
      fun w => (a.re : ℂ) * b w + Complex.I * ((a.im : ℂ) * b w) := by
    funext w
    conv_lhs => rw [← Complex.re_add_im a]
    ring
  rw [heq, compactDbarSolution_add (hreal _) (hsreal _)
    (contDiff_const.mul (hreal _)) ((hsreal _).comp_left (by simp)),
    compactDbarSolution_I_mul (hreal _) (hsreal _),
    compactDbarSolution_real_mul hb hsb, compactDbarSolution_real_mul hb hsb]
  funext z
  conv_rhs => rw [← Complex.re_add_im a]
  ring

theorem compactDbarSolution_neg {b : ℂ → ℂ}
    (hb : ContDiff ℝ ∞ b) (hsb : HasCompactSupport b) :
    compactDbarSolution (fun w => -b w) = fun z => -compactDbarSolution b z := by
  simpa using compactDbarSolution_const_mul hb hsb (-1)

theorem compactDbarSolution_linear {b c : ℂ → ℂ}
    (hb : ContDiff ℝ ∞ b) (hsb : HasCompactSupport b)
    (hc : ContDiff ℝ ∞ c) (hsc : HasCompactSupport c) (a d : ℂ) :
    compactDbarSolution (fun w => a * b w + d * c w) =
      fun z => a * compactDbarSolution b z + d * compactDbarSolution c z := by
  rw [compactDbarSolution_add (contDiff_const.mul hb) (hsb.comp_left (by simp))
    (contDiff_const.mul hc) (hsc.comp_left (by simp)),
    compactDbarSolution_const_mul hb hsb, compactDbarSolution_const_mul hc hsc]

end Yau.Blueprint.D05Proof
