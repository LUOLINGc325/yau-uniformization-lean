import Yau.LeafProofs.L05AutonomousSecondFTC

noncomputable section
open Filter Set MeasureTheory Matrix
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic Yau.LeafProofs.L05Aux

def autoTentWeight (s : ℝ) : ℝ := max (1-|s|) 0

theorem autoTentWeight_nonneg (s : ℝ) : 0≤ autoTentWeight s := le_max_right _ _

theorem autoTentWeight_continuous : Continuous autoTentWeight :=
  (continuous_const.sub continuous_abs).sup continuous_const

theorem autoTentWeight_support : Function.support autoTentWeight⊆Icc (-1 : ℝ) 1 := by
  intro s hs
  have habs : |s|< 1 := by
    by_contra hh
    exact hs (max_eq_right (sub_nonpos.mpr (le_of_not_gt hh)))
  exact ⟨(abs_lt.mp habs).1.le,(abs_lt.mp habs).2.le⟩

theorem autoTentWeight_compact : HasCompactSupport autoTentWeight :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc autoTentWeight_support

theorem autoTentWeight_integral_interval (g : ℝ → ℝ) :
    (∫ s, autoTentWeight s*g s)=∫ s in (-1 : ℝ)..1, (1-|s|)*g s := by
  have heq : (fun s => autoTentWeight s*g s)=
      (Ioc (-1 : ℝ) 1).indicator (fun s => (1-|s|)*g s) := by
    funext s
    by_cases hs : s∈Ioc (-1 : ℝ) 1
    · have hle : |s|≤ 1 := abs_le.mpr ⟨hs.1.le,hs.2⟩
      simp only [autoTentWeight,max_eq_left (sub_nonneg.mpr hle),indicator_of_mem hs]
    · have hge : 1≤ |s| := by
        by_cases hlo : s≤ -1
        · linarith only [hlo,neg_le_abs s]
        · have hhi : 1< s := by exact lt_of_not_ge (fun h => hs ⟨lt_of_not_ge hlo,h⟩)
          exact hhi.le.trans (le_abs_self s)
      simp only [autoTentWeight,max_eq_right (sub_nonpos.mpr hge),zero_mul,indicator_of_notMem hs]
  rw [heq,integral_indicator measurableSet_Ioc,intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ)≤ 1)]

theorem autoTentWeight_integral : (∫ s, autoTentWeight s)=1 := by
  have hpoly : ContDiff ℝ ∞ (fun s : ℝ => s^2) := contDiff_id.pow 2
  have hfirst : deriv (fun s : ℝ => s^2)=(fun s => 2*s) := by
    funext s
    simpa only [pow_one,mul_one,Nat.reduceSub,Nat.cast_ofNat,id_eq] using (hasDerivAt_pow 2 s).deriv
  have hsecond (s : ℝ) : deriv (deriv (fun s : ℝ => s^2)) s=2 := by
    rw [hfirst]
    simpa only [mul_one,id_eq] using ((hasDerivAt_id s).const_mul (2 : ℝ)).deriv
  have hh := auto_triangular_second_identity hpoly
  simp_rw [hsecond] at hh
  have hweight : (∫ s, autoTentWeight s)=∫ s in (-1 : ℝ)..1, 1-|s| := by
    simpa only [mul_one] using autoTentWeight_integral_interval (fun _ => 1)
  rw [hweight]
  rw [intervalIntegral.integral_mul_const] at hh
  norm_num only [one_pow,neg_one_sq,zero_pow (by norm_num : 2≠0),mul_zero,sub_zero] at hh
  linarith only [hh]

def autoTentMeasure : Measure ℝ := volume.withDensity (fun s => ENNReal.ofReal (autoTentWeight s))

theorem autoTentMeasure_isProbability : IsProbabilityMeasure autoTentMeasure := by
  constructor
  change (volume.withDensity (fun s => ENNReal.ofReal (autoTentWeight s))) univ=1
  rw [withDensity_apply _ MeasurableSet.univ,setLIntegral_univ,
    ← ofReal_integral_eq_lintegral_ofReal (autoTentWeight_continuous.integrable_of_hasCompactSupport autoTentWeight_compact)
      (ae_of_all volume autoTentWeight_nonneg),autoTentWeight_integral,ENNReal.ofReal_one]

theorem autoTentMeasure_integral (g : ℝ → ℝ) :
    (∫ s, g s ∂autoTentMeasure)=∫ s in (-1 : ℝ)..1, (1-|s|)*g s := by
  rw [autoTentMeasure,integral_withDensity_eq_integral_toReal_smul
    autoTentWeight_continuous.measurable.ennreal_ofReal (ae_of_all volume fun s => ENNReal.ofReal_lt_top) g]
  have heq : (fun s => (ENNReal.ofReal (autoTentWeight s)).toReal • g s)=(fun s => autoTentWeight s*g s) := by
    funext s
    rw [ENNReal.toReal_ofReal (autoTentWeight_nonneg s),smul_eq_mul]
  rw [heq,autoTentWeight_integral_interval]

theorem autoTentMeasure_interval_ae : ∀ᵐ s ∂autoTentMeasure, s∈Icc (-1 : ℝ) 1 := by
  change ∀ᵐ s ∂volume.withDensity (fun s => ENNReal.ofReal (autoTentWeight s)), _
  apply (ae_withDensity_iff autoTentWeight_continuous.measurable.ennreal_ofReal).mpr
  exact ae_of_all volume fun s hs => autoTentWeight_support (by
    intro hz
    exact hs (by rw [hz,ENNReal.ofReal_zero]))

theorem autoTentMeasure_continuous_integrable {g : ℝ → ℝ} (hg : Continuous g) :
    Integrable g autoTentMeasure := by
  let : IsProbabilityMeasure autoTentMeasure := autoTentMeasure_isProbability
  obtain ⟨t,ht,hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr (by norm_num : (-1 : ℝ)≤1)) hg.norm.continuousOn
  apply Integrable.of_bound hg.stronglyMeasurable.aestronglyMeasurable ‖g t‖
  filter_upwards [autoTentMeasure_interval_ae] with s hs
  exact hmax hs

/-- The square-mean estimate follows from the actual nonnegative variance integral. -/
theorem auto_probability_square_mean {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    {f : X → ℝ} (hf : Integrable f μ) (hf2 : Integrable (fun x => (f x)^2) μ) :
    (∫ x, f x ∂μ)^2≤ ∫ x, (f x)^2 ∂μ := by
  let m := ∫ x, f x ∂μ
  have hh : 0≤ ∫ x, (f x-m)^2 ∂μ := integral_nonneg fun x => sq_nonneg _
  have heq : (fun x => (f x-m)^2)=(fun x => (f x)^2-(2*m)*f x+m^2) := by
    funext x
    ring
  have hlin : Integrable (fun x => (2*m)*f x) μ := hf.const_mul _
  have hsplit₁ : (∫ x, ((f x)^2-(2*m)*f x+m^2) ∂μ)=
      (∫ x, ((f x)^2-(2*m)*f x) ∂μ)+(∫ _ : X, m^2 ∂μ) := by
    simpa only [Pi.sub_apply] using integral_add (hf2.sub hlin) (integrable_const (m^2))
  have hsplit₂ : (∫ x, ((f x)^2-(2*m)*f x) ∂μ)=
      (∫ x, (f x)^2 ∂μ)-(∫ x, (2*m)*f x ∂μ) := integral_sub hf2 hlin
  rw [heq,hsplit₁,hsplit₂,integral_const_mul,integral_const,probReal_univ,one_smul] at hh
  change 0≤(∫ x, (f x)^2 ∂μ)-2*m*m+m^2 at hh
  nlinarith only [hh]

/-- The exact second FTC identity is an average against an actual positive probability. -/
theorem auto_spatial_second_as_probability {n : ℕ} {f : Space n → ℝ} (hf : ContDiff ℝ ∞ f)
    (x e : Space n) {h : ℝ} (hh : h≠0) :
    autoSpatialSecond f e h x=
      ∫ s, fderiv ℝ (fderiv ℝ f) (x+(s*h) • e) e e ∂autoTentMeasure := by
  rw [autoTentMeasure_integral]
  exact auto_spatial_second_integral hf x e hh

/-- Actual Jensen, with no pointwise bound on the unknown Hessian in the hypotheses. -/
theorem auto_spatial_second_square_probability {n : ℕ} {f : Space n → ℝ} (hf : ContDiff ℝ ∞ f)
    (x e : Space n) {h : ℝ} (hh : h≠0) :
    (autoSpatialSecond f e h x)^2≤
      ∫ s, (fderiv ℝ (fderiv ℝ f) (x+(s*h) • e) e e)^2 ∂autoTentMeasure := by
  let : IsProbabilityMeasure autoTentMeasure := autoTentMeasure_isProbability
  have hH : Continuous (fun z : Space n => fderiv ℝ (fderiv ℝ f) z e e) :=
    ((((hf.fderiv_right (m := ∞) (by simp)).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).clm_apply
      contDiff_const).continuous
  have hpath : Continuous (fun s : ℝ => x+(s*h) • e) :=
    continuous_const.add ((continuous_id.mul continuous_const).smul continuous_const)
  have hcont := hH.comp hpath
  rw [auto_spatial_second_as_probability hf x e hh]
  exact auto_probability_square_mean autoTentMeasure (autoTentMeasure_continuous_integrable hcont)
    (autoTentMeasure_continuous_integrable (hcont.pow 2))

end Yau.LeafProofs.L05AutonomousAux
