import Yau.LeafProofs.L05AutonomousMollifierAverage
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Calculus.ContDiff.Deriv

noncomputable section
open Filter Set MeasureTheory Matrix
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic Yau.LeafProofs.L05Aux

/-- The genuine one-dimensional second FTC identity with the positive triangular weight. -/
theorem auto_triangular_second_identity {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) :
    g 1+g (-1)-2*g 0=∫ s in (-1 : ℝ)..1, (1-|s|)*deriv (deriv g) s := by
  have hgp := (contDiff_infty_iff_deriv.mp hg).2
  have hgpp := (contDiff_infty_iff_deriv.mp hgp).2
  have hderiv (s : ℝ) : HasDerivAt g (deriv g s) s := (hg.differentiable (by simp) s).hasDerivAt
  have hderivp (s : ℝ) : HasDerivAt (deriv g) (deriv (deriv g) s) s := (hgp.differentiable (by simp) s).hasDerivAt
  have hFTC (a b : ℝ) : (∫ s in a..b, deriv g s)=g b-g a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hderiv s) (hgp.continuous.intervalIntegrable a b)
  have hright : (∫ s in (0 : ℝ)..1, (1-s)*deriv (deriv g) s)=g 1-g 0-deriv g 0 := by
    have hh := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := (0 : ℝ)) (b := 1)
      (u := fun s : ℝ => 1-s) (u' := fun _ => (-1 : ℝ)) (v := deriv g) (v' := deriv (deriv g))
      (fun s _ => (hasDerivAt_id s).const_sub 1)
      (fun s _ => hderivp s) intervalIntegrable_const (hgpp.continuous.intervalIntegrable 0 1)
    rw [intervalIntegral.integral_const_mul,hFTC] at hh
    norm_num only [sub_self,zero_mul,sub_zero,one_mul,zero_sub] at hh
    linarith only [hh]
  have hleft : (∫ s in (-1 : ℝ)..0, (1+s)*deriv (deriv g) s)=g (-1)-g 0+deriv g 0 := by
    have hh := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := (-1 : ℝ)) (b := 0)
      (u := fun s : ℝ => 1+s) (u' := fun _ => (1 : ℝ)) (v := deriv g) (v' := deriv (deriv g))
      (fun s _ => (hasDerivAt_id s).const_add 1)
      (fun s _ => hderivp s) intervalIntegrable_const (hgpp.continuous.intervalIntegrable (-1) 0)
    rw [intervalIntegral.integral_const_mul,hFTC] at hh
    norm_num only [add_zero,add_neg_cancel,one_mul,zero_mul,sub_zero] at hh
    linarith only [hh]
  have hcont : Continuous (fun s : ℝ => (1-|s|)*deriv (deriv g) s) :=
    (continuous_const.sub continuous_abs).mul hgpp.continuous
  have hsum := intervalIntegral.integral_add_adjacent_intervals (μ := volume) (hcont.intervalIntegrable (-1) 0)
    (hcont.intervalIntegrable 0 1)
  have heqL : (∫ s in (-1 : ℝ)..0, (1-|s|)*deriv (deriv g) s)=
      ∫ s in (-1 : ℝ)..0, (1+s)*deriv (deriv g) s := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le (by norm_num : (-1 : ℝ)≤ 0)] at hs
    change (1-|s|)*deriv (deriv g) s=(1+s)*deriv (deriv g) s
    rw [abs_of_nonpos hs.2]
    ring
  have heqR : (∫ s in (0 : ℝ)..1, (1-|s|)*deriv (deriv g) s)=
      ∫ s in (0 : ℝ)..1, (1-s)*deriv (deriv g) s := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le (by norm_num : (0 : ℝ)≤ 1)] at hs
    change (1-|s|)*deriv (deriv g) s=(1-s)*deriv (deriv g) s
    rw [abs_of_nonneg hs.1]
  rw [heqL,heqR,hleft,hright] at hsum
  linarith only [hsum]

/-- Restriction to a real line preserves actual spatial first and second derivatives. -/
theorem auto_line_second_derivative {n : ℕ} {f : Space n → ℝ} (hf : ContDiff ℝ ∞ f)
    (x v : Space n) (s : ℝ) :
    deriv (deriv (fun t : ℝ => f (x+t • v))) s=
      fderiv ℝ (fderiv ℝ f) (x+s • v) v v := by
  have hfirst : deriv (fun t : ℝ => f (x+t • v))=(fun t => fderiv ℝ f (x+t • v) v) := by
    funext t
    exact (hf.differentiable (by simp) (x+t • v)).deriv_comp_add_smul
  have hD : DifferentiableAt ℝ (fderiv ℝ f) (x+s • v) :=
    (hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp) _
  have hdv : DifferentiableAt ℝ (fun y => fderiv ℝ f y v) (x+s • v) :=
    hD.clm_apply (differentiableAt_const v)
  rw [hfirst,hdv.deriv_comp_add_smul,fderiv_clm_apply hD (differentiableAt_const v)]
  simp

/-- The second difference is the literal integral of the genuine spatial Hessian. -/
theorem auto_spatial_second_identity {n : ℕ} {f : Space n → ℝ} (hf : ContDiff ℝ ∞ f)
    (x v : Space n) :
    f (x+v)+f (x-v)-2*f x=
      ∫ s in (-1 : ℝ)..1, (1-|s|)*fderiv ℝ (fderiv ℝ f) (x+s • v) v v := by
  have hg : ContDiff ℝ ∞ (fun t : ℝ => f (x+t • v)) :=
    hf.comp (contDiff_const.add (contDiff_id.smul contDiff_const))
  have hh := auto_triangular_second_identity hg
  simp_rw [auto_line_second_derivative hf x v] at hh
  simpa only [one_smul,neg_smul,one_smul,zero_smul,add_zero,sub_eq_add_neg] using hh

def autoSpatialSecond {n : ℕ} (f : Space n → ℝ) (e : Space n) (h : ℝ) (x : Space n) : ℝ :=
  (f (x+h • e)+f (x-h • e)-2*f x)/h^2

/-- The radius cancels algebraically; no limiting Hessian of the original rough function is assumed. -/
theorem auto_spatial_second_integral {n : ℕ} {f : Space n → ℝ} (hf : ContDiff ℝ ∞ f)
    (x e : Space n) {h : ℝ} (hh : h≠0) :
    autoSpatialSecond f e h x=
      ∫ s in (-1 : ℝ)..1, (1-|s|)*fderiv ℝ (fderiv ℝ f) (x+(s*h) • e) e e := by
  rw [autoSpatialSecond,auto_spatial_second_identity hf x (h • e),← intervalIntegral.integral_div]
  apply intervalIntegral.integral_congr
  intro s hs
  change ((1-|s|)*fderiv ℝ (fderiv ℝ f) (x+s • (h • e)) (h • e) (h • e))/h^2=_
  simp only [smul_smul,map_smul,ContinuousLinearMap.smul_apply,smul_eq_mul]
  field_simp

end Yau.LeafProofs.L05AutonomousAux
