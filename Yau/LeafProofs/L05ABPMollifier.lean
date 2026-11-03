import Yau.LeafProofs.L05ABPRegularization
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution

noncomputable section

open Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius Convolution

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic

local instance L05ABPMollifier_pointVolumeHaar (n : ℕ) :
    (volume : Measure (Point n)).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _

local instance L05ABPMollifier_secondNormSMul (n : ℕ) :
    NormSMulClass ℝ (Point n →L[ℝ] Point n →L[ℝ] ℝ) := by
  exact NormedSpace.toNormSMulClass (𝕜 := ℝ) (E := Point n →L[ℝ] Point n →L[ℝ] ℝ)

def abpBump (n : ℕ) : ContDiffBump (0 : Point n) := ⟨1/2,1,by norm_num,by norm_num⟩

def abpKernel (n : ℕ) : Point n → ℝ := (abpBump n).normed volume

def scaledKernel (n : ℕ) (r : ℝ) (x : Point n) : ℝ :=
  (r^Module.finrank ℝ (Point n))⁻¹*abpKernel n (r⁻¹ • x)

def abpMollify {n : ℕ} (r : ℝ) (u : Point n → ℝ) : Point n → ℝ :=
  scaledKernel n r ⋆[ContinuousLinearMap.lsmul ℝ ℝ,volume] u

theorem abpKernel_smooth (n : ℕ) : ContDiff ℝ ∞ (abpKernel n) :=
  (abpBump n).contDiff_normed

theorem abpKernel_nonneg (n : ℕ) (x : Point n) : 0≤abpKernel n x :=
  (abpBump n).nonneg_normed x

theorem abpKernel_integral (n : ℕ) : ∫ x, abpKernel n x = 1 :=
  (abpBump n).integral_normed

theorem abpKernel_neg (n : ℕ) (x : Point n) : abpKernel n (-x)=abpKernel n x :=
  (abpBump n).normed_neg x

theorem scaledKernel_nonneg {n : ℕ} {r : ℝ} (hr : 0<r) (x : Point n) :
    0 ≤ scaledKernel n r x := by
  exact mul_nonneg (inv_nonneg.mpr (pow_nonneg hr.le _)) (abpKernel_nonneg n _)

theorem scaledKernel_neg (n : ℕ) (r : ℝ) (x : Point n) :
    scaledKernel n r (-x)=scaledKernel n r x := by
  simp only [scaledKernel,smul_neg,abpKernel_neg]

theorem scaledKernel_smooth (n : ℕ) (r : ℝ) : ContDiff ℝ ∞ (scaledKernel n r) := by
  unfold scaledKernel
  have hk := abpKernel_smooth n
  fun_prop

theorem scaledKernel_support {n : ℕ} {r : ℝ} (hr : 0<r) :
    Function.support (scaledKernel n r) ⊆ Metric.ball (0 : Point n) r := by
  intro x hx
  have hk : abpKernel n (r⁻¹ • x)≠0 := by
    intro hz
    apply hx
    simp only [scaledKernel,hz,mul_zero]
  have hball : r⁻¹ • x ∈ Metric.ball (0 : Point n) 1 := by
    have hsup : r⁻¹ • x ∈ Function.support ((abpBump n).normed volume) := hk
    rw [(abpBump n).support_normed_eq] at hsup
    exact hsup
  have hn : ‖x‖/r<1 := by
    simpa only [Metric.mem_ball,dist_eq_norm,sub_zero,norm_smul,Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hr),div_eq_mul_inv,mul_comm] using hball
  have hn' : ‖x‖<r := by simpa only [one_mul] using (div_lt_iff₀ hr).mp hn
  simpa only [Metric.mem_ball,dist_eq_norm,sub_zero] using hn'

theorem scaledKernel_compactSupport {n : ℕ} {r : ℝ} (hr : 0<r) :
    HasCompactSupport (scaledKernel n r) := by
  change IsCompact (closure (Function.support (scaledKernel n r)))
  apply (isCompact_closedBall (0 : Point n) r).of_isClosed_subset isClosed_closure
  exact closure_minimal ((scaledKernel_support hr).trans Metric.ball_subset_closedBall)
    Metric.isClosed_closedBall

theorem scaledKernel_integral {n : ℕ} {r : ℝ} (hr : 0<r) :
    ∫ x, scaledKernel n r x = 1 := by
  unfold scaledKernel
  rw [integral_const_mul,Measure.integral_comp_inv_smul volume (abpKernel n) r,
    abpKernel_integral,smul_eq_mul,mul_one,abs_of_pos (pow_pos hr _)]
  exact inv_mul_cancel₀ (pow_ne_zero _ hr.ne')

theorem abpMollify_smooth {n : ℕ} {u : Point n → ℝ} {r : ℝ} (hr : 0<r)
    (hu : Continuous u) : ContDiff ℝ ∞ (abpMollify r u) := by
  exact (scaledKernel_compactSupport hr).contDiff_convolution_left _
    (scaledKernel_smooth n r) hu.locallyIntegrable

theorem abpMollify_approx {n : ℕ} {u : Point n → ℝ} {r eta : ℝ} (hr : 0<r)
    (heta : 0≤eta) (hu : AEStronglyMeasurable u volume) (z : Point n)
    (hlocal : ∀ y ∈ Metric.ball z r, dist (u y) (u z)≤eta) :
    dist (abpMollify r u z) (u z)≤eta := by
  exact dist_convolution_le heta (scaledKernel_support hr) (scaledKernel_nonneg hr)
    (scaledKernel_integral hr) hu hlocal

theorem scaledKernel_fderiv (n : ℕ) (r : ℝ) (x : Point n) :
    fderiv ℝ (scaledKernel n r) x=
      ((r^Module.finrank ℝ (Point n))⁻¹*r⁻¹) • fderiv ℝ (abpKernel n) (r⁻¹ • x) := by
  have hs : HasFDerivAt (fun y : Point n => r⁻¹ • y)
      (r⁻¹ • ContinuousLinearMap.id ℝ (Point n)) x :=
    (hasFDerivAt_id x).const_smul r⁻¹
  have hk := ((abpKernel_smooth n).differentiable (by simp) (r⁻¹ • x)).hasFDerivAt
  have hd := (hk.comp x hs).const_mul ((r^Module.finrank ℝ (Point n))⁻¹)
  convert! hd.fderiv using 1
  apply ContinuousLinearMap.ext
  intro v
  simp [smul_smul]

theorem scaledKernel_secondFDeriv (n : ℕ) (r : ℝ) (x : Point n) :
    fderiv ℝ (fderiv ℝ (scaledKernel n r)) x=
      (((r^Module.finrank ℝ (Point n))⁻¹*r⁻¹)*r⁻¹) •
        fderiv ℝ (fderiv ℝ (abpKernel n)) (r⁻¹ • x) := by
  have he : fderiv ℝ (scaledKernel n r)=fun y =>
      ((r^Module.finrank ℝ (Point n))⁻¹*r⁻¹) • fderiv ℝ (abpKernel n) (r⁻¹ • y) :=
    funext (scaledKernel_fderiv n r)
  rw [he]
  have hs : HasFDerivAt (fun y : Point n => r⁻¹ • y)
      (r⁻¹ • ContinuousLinearMap.id ℝ (Point n)) x :=
    (hasFDerivAt_id x).const_smul r⁻¹
  have hgSmooth : ContDiff ℝ ∞ (fderiv ℝ (abpKernel n)) :=
    (abpKernel_smooth n).fderiv_right (by simp)
  have hg := (hgSmooth.differentiable (by simp) (r⁻¹ • x)).hasFDerivAt
  have hd := (hg.comp x hs).const_smul ((r^Module.finrank ℝ (Point n))⁻¹*r⁻¹)
  convert! hd.fderiv using 1
  apply ContinuousLinearMap.ext
  intro v
  simp [smul_smul]

theorem scaledKernel_fderiv_norm_integral {n : ℕ} {r : ℝ} (hr : 0<r) :
    (∫ x, ‖fderiv ℝ (scaledKernel n r) x‖)=
      r⁻¹*(∫ x, ‖fderiv ℝ (abpKernel n) x‖) := by
  have hc : 0≤(r^Module.finrank ℝ (Point n))⁻¹*r⁻¹ := by positivity
  simp_rw [scaledKernel_fderiv,norm_smul,Real.norm_eq_abs,abs_of_nonneg hc]
  rw [integral_const_mul,
    Measure.integral_comp_inv_smul volume (fun x => ‖fderiv ℝ (abpKernel n) x‖) r]
  simp only [abs_of_pos (pow_pos hr _),smul_eq_mul]
  field_simp

theorem scaledKernel_secondFDeriv_norm_integral {n : ℕ} {r : ℝ} (hr : 0<r) :
    (∫ x, ‖fderiv ℝ (fderiv ℝ (scaledKernel n r)) x‖)=
      (r⁻¹*r⁻¹)*(∫ x, ‖fderiv ℝ (fderiv ℝ (abpKernel n)) x‖) := by
  have hc : 0≤((r^Module.finrank ℝ (Point n))⁻¹*r⁻¹)*r⁻¹ := by positivity
  simp only [scaledKernel_secondFDeriv]
  have hn (x : Point n) :
      ‖(((r^Module.finrank ℝ (Point n))⁻¹*r⁻¹)*r⁻¹) •
        fderiv ℝ (fderiv ℝ (abpKernel n)) (r⁻¹ • x)‖ =
      (((r^Module.finrank ℝ (Point n))⁻¹*r⁻¹)*r⁻¹)*
        ‖fderiv ℝ (fderiv ℝ (abpKernel n)) (r⁻¹ • x)‖ := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hc]
  simp_rw [hn]
  rw [integral_const_mul,
    Measure.integral_comp_inv_smul volume (fun x => ‖fderiv ℝ (fderiv ℝ (abpKernel n)) x‖) r]
  simp only [abs_of_pos (pow_pos hr _),smul_eq_mul]
  field_simp

theorem scaledKernel_linear_integral_zero (n : ℕ) (r : ℝ) (l : Point n →L[ℝ] ℝ) :
    (∫ x, scaledKernel n r x*l x)=0 := by
  have hn := integral_neg_eq_self (fun x => scaledKernel n r x*l x) volume
  simp only [scaledKernel_neg,map_neg,mul_neg,integral_neg] at hn
  linarith

theorem abpMollify_hasFDerivAt {n : ℕ} {u : Point n → ℝ} {r : ℝ} (hr : 0<r)
    (hu : Continuous u) (z : Point n) :
    HasFDerivAt (abpMollify r u)
      ((fderiv ℝ (scaledKernel n r) ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).precompL (Point n),volume] u) z) z := by
  exact (scaledKernel_compactSupport hr).hasFDerivAt_convolution_left _
    ((scaledKernel_smooth n r).of_le (by simp)) hu.locallyIntegrable z

theorem abpMollify_secondFDeriv {n : ℕ} {u : Point n → ℝ} {r : ℝ} (hr : 0<r)
    (hu : Continuous u) (z : Point n) :
    fderiv ℝ (fderiv ℝ (abpMollify r u)) z=
      ∫ x, u (z-x) • fderiv ℝ (fderiv ℝ (scaledKernel n r)) x := by
  have he : fderiv ℝ (abpMollify r u)=
      fderiv ℝ (scaledKernel n r) ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).precompL (Point n),volume] u := by
    funext y
    exact (abpMollify_hasFDerivAt hr hu y).fderiv
  rw [he]
  have hkg : ContDiff ℝ ∞ (fderiv ℝ (scaledKernel n r)) :=
    (scaledKernel_smooth n r).fderiv_right (by simp)
  have hd := ((scaledKernel_compactSupport hr).fderiv (𝕜 := ℝ)).hasFDerivAt_convolution_left
    ((ContinuousLinearMap.lsmul ℝ ℝ).precompL (Point n))
    (hkg.of_le (show (1 : ℕ∞)≤∞ by simp)) (hu.locallyIntegrable (μ := volume)) z
  rw [hd.fderiv]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  simp only [ContinuousLinearMap.precompL_apply,ContinuousLinearMap.lsmul_apply,
    smul_apply,smul_eq_mul,mul_comm]

theorem abpMollify_fderiv_integral {n : ℕ} {u : Point n → ℝ} {r : ℝ} (hr : 0<r)
    (hu : Continuous u) (z : Point n) :
    fderiv ℝ (abpMollify r u) z=∫ x, u (z-x) • fderiv ℝ (scaledKernel n r) x := by
  rw [(abpMollify_hasFDerivAt hr hu z).fderiv]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  apply ContinuousLinearMap.ext
  intro v
  simp only [ContinuousLinearMap.precompL_apply,ContinuousLinearMap.lsmul_apply,
    smul_apply,smul_eq_mul,mul_comm]

theorem abpMollify_secondFDeriv_integral {n : ℕ} {u : Point n → ℝ} {r : ℝ} (hr : 0<r)
    (hu : Continuous u) (z : Point n) :
    fderiv ℝ (fderiv ℝ (abpMollify r u)) z=
      ∫ x, u (z-x) • fderiv ℝ (fderiv ℝ (scaledKernel n r)) x := by
  exact abpMollify_secondFDeriv hr hu z

theorem integral_compact_field_bound {n : ℕ} {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {u : Point n → ℝ} {k : Point n → F} {r c : ℝ}
    (hu : Continuous u) (hk : Continuous k)
    (hsupport : Function.support k ⊆ Metric.closedBall (0 : Point n) r)
    (z : Point n) (hlocal : ∀ x ∈ Metric.closedBall (0 : Point n) r, |u (z-x)|≤c) :
    ‖∫ x, u (z-x) • k x‖ ≤ c*(∫ x, ‖k x‖) := by
  have hkc : HasCompactSupport k := by
    change IsCompact (closure (Function.support k))
    exact (isCompact_closedBall (0 : Point n) r).of_isClosed_subset isClosed_closure
      (closure_minimal hsupport Metric.isClosed_closedBall)
  have hki := hk.integrable_of_hasCompactSupport hkc (μ := volume)
  have hfc : Continuous (fun x => u (z-x) • k x) :=
    (hu.comp (continuous_const.sub continuous_id)).smul hk
  have hfi := hfc.integrable_of_hasCompactSupport hkc.smul_left (μ := volume)
  have hpoint (x : Point n) : ‖u (z-x) • k x‖≤c*‖k x‖ := by
    by_cases hx : k x=0
    · simp [hx]
    · rw [norm_smul,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hlocal x (hsupport hx)) (norm_nonneg _)
  calc
    _ ≤ ∫ x, ‖u (z-x) • k x‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ x, c*‖k x‖ := integral_mono hfi.norm (hki.norm.const_mul c) hpoint
    _ = _ := integral_const_mul _ _

theorem scaledKernel_tsupport {n : ℕ} {r : ℝ} (hr : 0<r) :
    tsupport (scaledKernel n r) ⊆ Metric.closedBall (0 : Point n) r :=
  closure_minimal ((scaledKernel_support hr).trans Metric.ball_subset_closedBall)
    Metric.isClosed_closedBall

theorem abpMollify_fderiv_local_bound {n : ℕ} {u : Point n → ℝ} {r c : ℝ}
    (hr : 0<r) (hu : Continuous u) (z : Point n)
    (hlocal : ∀ x ∈ Metric.closedBall (0 : Point n) r, |u (z-x)|≤c) :
    ‖fderiv ℝ (abpMollify r u) z‖≤c*r⁻¹*(∫ x, ‖fderiv ℝ (abpKernel n) x‖) := by
  rw [abpMollify_fderiv_integral hr hu z]
  have hb := integral_compact_field_bound hu
    ((scaledKernel_smooth n r).continuous_fderiv (by simp))
    ((support_fderiv_subset ℝ).trans (scaledKernel_tsupport hr)) z hlocal
  rw [scaledKernel_fderiv_norm_integral hr] at hb
  simpa only [mul_assoc] using hb

theorem abpMollify_secondFDeriv_local_bound {n : ℕ} {u : Point n → ℝ} {r c : ℝ}
    (hr : 0<r) (hu : Continuous u) (z : Point n)
    (hlocal : ∀ x ∈ Metric.closedBall (0 : Point n) r, |u (z-x)|≤c) :
    ‖fderiv ℝ (fderiv ℝ (abpMollify r u)) z‖≤
      c*(r⁻¹*r⁻¹)*(∫ x, ‖fderiv ℝ (fderiv ℝ (abpKernel n)) x‖) := by
  rw [abpMollify_secondFDeriv_integral hr hu z]
  have hkg : ContDiff ℝ ∞ (fderiv ℝ (scaledKernel n r)) :=
    (scaledKernel_smooth n r).fderiv_right (by simp)
  have hb := integral_compact_field_bound hu (hkg.continuous_fderiv (by simp))
    ((support_fderiv_subset ℝ).trans ((tsupport_fderiv_subset ℝ).trans (scaledKernel_tsupport hr))) z hlocal
  rw [scaledKernel_secondFDeriv_norm_integral hr] at hb
  simpa only [mul_assoc] using hb

theorem abpMollify_integrand_integrable {n : ℕ} {u : Point n → ℝ} {r : ℝ}
    (hr : 0<r) (hu : Continuous u) (z : Point n) :
    Integrable (fun x => scaledKernel n r x*u (z-x)) := by
  have hc : Continuous (fun x => scaledKernel n r x*u (z-x)) :=
    (scaledKernel_smooth n r).continuous.mul (hu.comp (continuous_const.sub continuous_id))
  exact hc.integrable_of_hasCompactSupport (scaledKernel_compactSupport hr).mul_right

theorem abpMollify_sub {n : ℕ} {u v : Point n → ℝ} {r : ℝ} (hr : 0<r)
    (hu : Continuous u) (hv : Continuous v) :
    abpMollify r (u-v)=abpMollify r u-abpMollify r v := by
  funext z
  change (∫ x, scaledKernel n r x*(u (z-x)-v (z-x)))=
    (∫ x, scaledKernel n r x*u (z-x))-(∫ x, scaledKernel n r x*v (z-x))
  simp_rw [mul_sub]
  exact integral_sub (abpMollify_integrand_integrable hr hu z) (abpMollify_integrand_integrable hr hv z)

theorem abpMollify_const {n : ℕ} {r : ℝ} (hr : 0<r) (c : ℝ) :
    abpMollify (n := n) r (fun _ => c)=fun _ => c := by
  funext z
  change (∫ x, scaledKernel n r x*c)=c
  rw [integral_mul_const,scaledKernel_integral hr,one_mul]

end Yau.LeafProofs.L05Aux
