import Yau.LeafProofs.L16HalfSpaceHolderExtension

open MeasureTheory Filter
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1000000
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates

/-- The normalized one-dimensional heat kernel in the normal coordinate. -/
def normalGaussianKernel (t a : ℝ) : ℝ :=
  (Real.sqrt (4*Real.pi*t))⁻¹*Real.exp (-(4*t)⁻¹*a^2)

theorem normalGaussianKernel_pos {t : ℝ} (ht : 0 < t) (a : ℝ) :
    0 < normalGaussianKernel t a := by
  dsimp only [normalGaussianKernel]
  positivity

theorem normalGaussianKernel_integrable {t : ℝ} (ht : 0 < t) :
    Integrable (normalGaussianKernel t) := by
  exact (integrable_exp_neg_mul_sq (by positivity : 0 < (4*t)⁻¹)).const_mul _

theorem normalGaussianKernel_integral {t : ℝ} (ht : 0 < t) :
    ∫ a : ℝ, normalGaussianKernel t a = 1 := by
  have harg : Real.pi/(4*t)⁻¹ = 4*Real.pi*t := by rw [div_inv_eq_mul]; ring
  change (∫ a : ℝ, (Real.sqrt (4*Real.pi*t))⁻¹*Real.exp (-(4*t)⁻¹*a^2)) = 1
  rw [integral_const_mul,integral_gaussian,harg]
  exact inv_mul_cancel₀ (ne_of_gt (Real.sqrt_pos.2 (by positivity)))

theorem normalGaussianKernel_integral_Ioi {t : ℝ} (ht : 0 < t) :
    ∫ a in Set.Ioi (0 : ℝ), normalGaussianKernel t a = 1/2 := by
  have harg : Real.pi/(4*t)⁻¹ = 4*Real.pi*t := by rw [div_inv_eq_mul]; ring
  change (∫ a in Set.Ioi (0 : ℝ), (Real.sqrt (4*Real.pi*t))⁻¹*Real.exp (-(4*t)⁻¹*a^2)) = 1/2
  rw [integral_const_mul,integral_gaussian_Ioi,harg]
  rw [← mul_div_assoc,inv_mul_cancel₀ (ne_of_gt (Real.sqrt_pos.2 (by positivity)))]

theorem normalGaussianKernel_even (t a : ℝ) :
    normalGaussianKernel t (-a) = normalGaussianKernel t a := by
  simp only [normalGaussianKernel,neg_sq]

theorem normalGaussianKernel_spatial_smooth (t : ℝ) : ContDiff ℝ ∞ (normalGaussianKernel t) := by
  change ContDiff ℝ ∞ (fun a : ℝ => (Real.sqrt (4*Real.pi*t))⁻¹*Real.exp (-(4*t)⁻¹*a^2))
  fun_prop

theorem normalGaussianKernel_hasDerivAt (t a : ℝ) :
    HasDerivAt (normalGaussianKernel t) (-(a/(2*t))*normalGaussianKernel t a) a := by
  convert ((((hasDerivAt_id a).pow 2).const_mul (-(4*t)⁻¹)).exp.const_mul
    (Real.sqrt (4*Real.pi*t))⁻¹) using 1
  · rfl
  · dsimp only [normalGaussianKernel,id_eq,Pi.pow_apply]
    simp only [Nat.cast_ofNat,mul_one,div_eq_mul_inv,mul_inv_rev]
    ring

/-- The actual erf profile, defined by its Gaussian primitive. -/
def normalHeatProfile (t a : ℝ) : ℝ := 2*∫ s in (0 : ℝ)..a, normalGaussianKernel t s

theorem normalHeatProfile_zero (t : ℝ) : normalHeatProfile t 0 = 0 := by
  simp only [normalHeatProfile,intervalIntegral.integral_same,mul_zero]

theorem normalHeatProfile_hasDerivAt (t a : ℝ) :
    HasDerivAt (normalHeatProfile t) (2*normalGaussianKernel t a) a := by
  exact (intervalIntegral.integral_hasDerivAt_right
    ((normalGaussianKernel_spatial_smooth t).continuous.intervalIntegrable 0 a)
    ((normalGaussianKernel_spatial_smooth t).continuous.stronglyMeasurableAtFilter volume (𝓝 a))
    ((normalGaussianKernel_spatial_smooth t).continuous.continuousAt)).const_mul 2


theorem normalHeatProfile_bounds {t a : ℝ} (ht : 0 < t) (ha : 0 ≤ a) :
    0 ≤ normalHeatProfile t a ∧ normalHeatProfile t a ≤ 1 := by
  have hPositive := intervalIntegral.integral_nonneg_of_forall (μ := volume) ha
    (fun z => (normalGaussianKernel_pos ht z).le)
  rw [intervalIntegral.integral_of_le ha] at hPositive
  have hMeasure : volume.restrict (Set.Ioc 0 a) ≤ volume.restrict (Set.Ioi (0 : ℝ)) :=
    Measure.restrict_mono_set volume (fun _ hy => hy.1)
  have hMass := integral_mono_measure hMeasure
    (Filter.Eventually.of_forall fun z => (normalGaussianKernel_pos ht z).le)
    (normalGaussianKernel_integrable ht).integrableOn
  rw [normalGaussianKernel_integral_Ioi ht] at hMass
  rw [normalHeatProfile,intervalIntegral.integral_of_le ha]
  constructor <;> linarith

/-- The positive Poisson kernel in the normal variable. -/
def normalPoissonKernel (a t : ℝ) : ℝ := (a/t)*normalGaussianKernel t a

theorem normalPoissonKernel_nonneg {a t : ℝ} (ha : 0 ≤ a) (ht : 0 < t) :
    0 ≤ normalPoissonKernel a t := by
  exact mul_nonneg (div_nonneg ha ht.le) (normalGaussianKernel_pos ht a).le

theorem normalHeatProfile_deriv (t : ℝ) :
    deriv (normalHeatProfile t) = fun a => 2*normalGaussianKernel t a := by
  funext a
  exact (normalHeatProfile_hasDerivAt t a).deriv

theorem normalHeatProfile_second_hasDerivAt (t a : ℝ) :
    HasDerivAt (deriv (normalHeatProfile t)) (-normalPoissonKernel a t) a := by
  rw [normalHeatProfile_deriv]
  convert (normalGaussianKernel_hasDerivAt t a).const_mul 2 using 1
  simp only [normalPoissonKernel,div_eq_mul_inv,mul_inv_rev]
  ring

theorem normalHeatProfile_tendsto_one {t : ℝ} (ht : 0 < t) :
    Tendsto (normalHeatProfile t) atTop (𝓝 1) := by
  have h := (intervalIntegral_tendsto_integral_Ioi (0 : ℝ)
    (normalGaussianKernel_integrable ht).integrableOn tendsto_id).const_mul 2
  rw [normalGaussianKernel_integral_Ioi ht] at h
  change Tendsto (fun a : ℝ => 2*∫ s in (0 : ℝ)..a, normalGaussianKernel t s) atTop (𝓝 1)
  convert h using 1 <;> norm_num


theorem normalGaussianKernel_sqrt_scaling {t : ℝ} (ht : 0 < t) (a : ℝ) :
    normalGaussianKernel t (Real.sqrt t*a)*Real.sqrt t = normalGaussianKernel 1 a := by
  have hs : Real.sqrt (4*Real.pi*t) = Real.sqrt (4*Real.pi)*Real.sqrt t :=
    Real.sqrt_mul (by positivity) t
  have hExp : -(4*t)⁻¹*(Real.sqrt t*a)^2 = -(4 : ℝ)⁻¹*a^2 := by
    rw [mul_pow,Real.sq_sqrt ht.le]
    field_simp
  change (Real.sqrt (4*Real.pi*t))⁻¹ *
    Real.exp (-(4*t)⁻¹*(Real.sqrt t*a)^2)*Real.sqrt t =
    (Real.sqrt (4*Real.pi*1))⁻¹*Real.exp (-(4*(1:ℝ))⁻¹*a^2)
  rw [hExp,hs]
  simp only [mul_one,mul_inv_rev]
  field_simp [ne_of_gt (Real.sqrt_pos.2 ht)]


theorem normalHeatProfile_sqrt_scaling {t : ℝ} (ht : 0 < t) (a : ℝ) :
    normalHeatProfile t a = normalHeatProfile 1 (a/Real.sqrt t) := by
  have hNonzero : Real.sqrt t ≠ 0 := ne_of_gt (Real.sqrt_pos.2 ht)
  have hUpper : Real.sqrt t*(a/Real.sqrt t) = a := by field_simp
  have hChange := intervalIntegral.smul_integral_comp_mul_left
    (f := normalGaussianKernel t) (a := 0) (b := a/Real.sqrt t) (Real.sqrt t)
  rw [smul_eq_mul,mul_zero,hUpper] at hChange
  calc
    normalHeatProfile t a = 2*(Real.sqrt t*∫ z in (0 : ℝ)..a/Real.sqrt t,
        normalGaussianKernel t (Real.sqrt t*z)) := by
      rw [hChange]
      rfl
    _ = 2*∫ z in (0 : ℝ)..a/Real.sqrt t, normalGaussianKernel 1 z := by
      rw [← intervalIntegral.integral_const_mul]
      congr 1
      apply intervalIntegral.integral_congr
      intro z _hz
      simpa only [mul_comm] using normalGaussianKernel_sqrt_scaling ht z
    _ = normalHeatProfile 1 (a/Real.sqrt t) := rfl

theorem normalHeatProfile_time_hasDerivAt {t : ℝ} (ht : 0 < t) (a : ℝ) :
    HasDerivAt (fun r => normalHeatProfile r a) (-normalPoissonKernel a t) t := by
  have hArg := (hasDerivAt_const t a).div (Real.hasDerivAt_sqrt ht.ne')
    (ne_of_gt (Real.sqrt_pos.2 ht))
  have hComp := (normalHeatProfile_hasDerivAt 1 (a/Real.sqrt t)).comp t hArg
  have hEq : (fun r => normalHeatProfile r a) =ᶠ[𝓝 t]
      (fun r => normalHeatProfile 1 (a/Real.sqrt r)) := by
    filter_upwards [eventually_gt_nhds ht] with r hr
    exact normalHeatProfile_sqrt_scaling hr a
  have hSc := normalGaussianKernel_sqrt_scaling ht (a/Real.sqrt t)
  have hPoint : Real.sqrt t*(a/Real.sqrt t) = a := by field_simp
  rw [hPoint] at hSc
  apply hEq.hasDerivAt_iff.mpr
  convert hComp using 1
  · rfl
  · dsimp only [normalPoissonKernel]
    rw [← hSc]
    field_simp [ht.ne',ne_of_gt (Real.sqrt_pos.2 ht)]
    rw [Real.sq_sqrt ht.le]
    ring


theorem normalHeatProfile_tendsto_initial_one {a : ℝ} (ha : 0 < a) :
    Tendsto (fun t => normalHeatProfile t a) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  apply tendsto_nhdsGT_zero_of_comp_inv_tendsto_atTop
  have hArg : Tendsto (fun t : ℝ => a*Real.sqrt t) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos ha).2 Real.tendsto_sqrt_atTop
  have h := (normalHeatProfile_tendsto_one (by norm_num : (0 : ℝ) < 1)).comp hArg
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [normalHeatProfile_sqrt_scaling (inv_pos.2 ht),Real.sqrt_inv,div_inv_eq_mul]
  rfl

theorem normalHeatProfile_tendsto_time_infty (a : ℝ) :
    Tendsto (fun t => normalHeatProfile t a) atTop (𝓝 0) := by
  have hArg : Tendsto (fun t : ℝ => a/Real.sqrt t) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero,Function.comp_def] using
      (tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop).const_mul a
  have h := (normalHeatProfile_hasDerivAt 1 0).continuousAt.tendsto.comp hArg
  rw [normalHeatProfile_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  exact (normalHeatProfile_sqrt_scaling ht a).symm


theorem normalPoissonKernel_probability {a : ℝ} (ha : 0 < a) :
    IntegrableOn (normalPoissonKernel a) (Set.Ioi 0) ∧
      (∫ t in Set.Ioi (0 : ℝ), normalPoissonKernel a t) = 1 := by
  let v : ℝ → ℝ := fun t => if t = 0 then 1 else normalHeatProfile t a
  have hv0 : v 0 = 1 := by simp only [v,ite_eq_left rfl]
  have hEqInitial : v =ᶠ[𝓝[>] (0 : ℝ)] (fun t => normalHeatProfile t a) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact ite_eq_right (ne_of_gt ht)
  have hInitial : Tendsto v (𝓝[>] (0 : ℝ)) (𝓝 1) :=
    (normalHeatProfile_tendsto_initial_one ha).congr' hEqInitial.symm
  have hCont : ContinuousWithinAt v (Set.Ici 0) 0 := by
    rw [← Set.Ioi_insert,continuousWithinAt_insert_self]
    change Tendsto v (𝓝[>] (0 : ℝ)) (𝓝 (v 0))
    rw [hv0]
    exact hInitial
  have hDeriv : ∀ t ∈ Set.Ioi (0 : ℝ), HasDerivAt v (-normalPoissonKernel a t) t := by
    intro t ht
    have hEq : v =ᶠ[𝓝 t] (fun r => normalHeatProfile r a) := by
      filter_upwards [eventually_gt_nhds ht] with r hr
      exact ite_eq_right (ne_of_gt hr)
    exact hEq.hasDerivAt_iff.mpr (normalHeatProfile_time_hasDerivAt ht a)
  have hNonpos : ∀ t ∈ Set.Ioi (0 : ℝ), -normalPoissonKernel a t ≤ 0 :=
    fun t ht => neg_nonpos.mpr (normalPoissonKernel_nonneg ha.le ht)
  have hEnd : Tendsto v atTop (𝓝 0) := by
    apply (normalHeatProfile_tendsto_time_infty a).congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    exact (ite_eq_right (ne_of_gt ht)).symm
  have hInt := integrableOn_Ioi_deriv_of_nonpos hCont hDeriv hNonpos hEnd
  have hValue := integral_Ioi_of_hasDerivAt_of_nonpos hCont hDeriv hNonpos hEnd
  have hPositiveInt : IntegrableOn (normalPoissonKernel a) (Set.Ioi 0) := by
    have hDouble := hInt.neg
    change IntegrableOn (fun t => - -normalPoissonKernel a t) (Set.Ioi 0) at hDouble
    simpa only [neg_neg] using hDouble
  refine ⟨hPositiveInt,?_⟩
  rw [integral_neg,hv0] at hValue
  linarith

end Yau.LeafProofs.L16Aux
