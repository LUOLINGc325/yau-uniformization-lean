import spec.CHAIN.LeafObligations
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

noncomputable section

open Filter MeasureTheory
open scoped Topology

namespace Yau.LeafProofs.L05Aux

def diniTransform (φ : ℝ → ℝ) (r : ℝ) : ℝ :=
  φ r + (∫ s in (0 : ℝ)..min (2*r) 1, φ s / s) +
    r * (∫ s in r..(1 : ℝ), φ s / s^2) + r*φ 1

def diniPowerConstant (σ : ℝ) : ℝ := 3 + (2 : ℝ)^σ/σ + 1/(1-σ)

def powerBound (η B : ℝ) (φ : ℝ → ℝ) : Prop :=
  ∀ r ∈ Set.Ioc (0 : ℝ) 1, 0 ≤ φ r ∧ φ r ≤ B*r^η

def diniIntegrable (φ : ℝ → ℝ) (r : ℝ) : Prop :=
  IntervalIntegrable (fun s => φ s/s) volume 0 (min (2*r) 1) ∧
    IntervalIntegrable (fun s => φ s/s^2) volume r 1

theorem power_div_self_eq {σ s : ℝ} (hs : 0 ≤ s) (hσ : σ ≠ 1) :
    s^σ / s = s^(σ-1) := by
  rw [Real.rpow_sub' hs (sub_ne_zero.mpr hσ), Real.rpow_one]

theorem power_div_sq_eq {σ s : ℝ} (hs : 0 ≤ s) (hσ : σ ≠ 2) :
    s^σ / s^2 = s^(σ-2) := by
  rw [Real.rpow_sub' hs (sub_ne_zero.mpr hσ), Real.rpow_two]

theorem diniPower_near_integrable {σ u : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (hu : 0 ≤ u) : IntervalIntegrable (fun s : ℝ => s^σ/s) volume 0 u := by
  refine (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < σ-1)).congr ?_
  intro s hs
  have hs' : s ∈ Set.Ioc 0 u := by simpa only [Set.uIoc_of_le hu] using hs
  exact (power_div_self_eq hs'.1.le
    (ne_of_lt hσ1)).symm

theorem diniPower_far_integrable {σ r : ℝ} (hσ1 : σ < 1)
    (hr : 0 < r) (hr1 : r ≤ 1) :
    IntervalIntegrable (fun s : ℝ => s^σ/s^2) volume r 1 := by
  have hn : (0 : ℝ) ∉ Set.uIcc r 1 := by simp [Set.uIcc_of_le hr1, hr.not_ge]
  refine (intervalIntegral.intervalIntegrable_rpow (r := σ-2) (Or.inr hn)).congr ?_
  intro s hs
  have hs' : s ∈ Set.Ioc r 1 := by simpa only [Set.uIoc_of_le hr1] using hs
  have hs0 : 0 ≤ s := hr.le.trans hs'.1.le
  exact (power_div_sq_eq hs0 (by linarith : σ ≠ 2)).symm

theorem diniPower_near_integral {σ u : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (hu : 0 ≤ u) : (∫ s in (0 : ℝ)..u, s^σ/s) = u^σ/σ := by
  calc
    _ = ∫ s in (0 : ℝ)..u, s^(σ-1) := by
      apply intervalIntegral.integral_congr
      intro s hs
      have hs' : s ∈ Set.Icc 0 u := by simpa only [Set.uIcc_of_le hu] using hs
      exact power_div_self_eq hs'.1 (ne_of_lt hσ1)
    _ = _ := by
      rw [integral_rpow (Or.inl (by linarith : -1 < σ-1))]
      simp [Real.zero_rpow hσ0.ne']

theorem diniPower_far_integral {σ r : ℝ} (hσ1 : σ < 1)
    (hr : 0 < r) (hr1 : r ≤ 1) :
    (∫ s in r..(1 : ℝ), s^σ/s^2) = (r^(σ-1)-1)/(1-σ) := by
  have hn : (0 : ℝ) ∉ Set.uIcc r 1 := by simp [Set.uIcc_of_le hr1, hr.not_ge]
  calc
    _ = ∫ s in r..(1 : ℝ), s^(σ-2) := by
      apply intervalIntegral.integral_congr
      intro s hs
      have hs' : s ∈ Set.Icc r 1 := by simpa only [Set.uIcc_of_le hr1] using hs
      exact power_div_sq_eq (hr.le.trans hs'.1)
        (by linarith : σ ≠ 2)
    _ = _ := by
      rw [integral_rpow (Or.inr ⟨by linarith,hn⟩)]
      have he : σ-2+1 = σ-1 := by ring
      rw [he, Real.one_rpow]
      field_simp [sub_ne_zero.mpr hσ1.ne, sub_ne_zero.mpr hσ1.ne']
      ring

theorem diniTransform_power_le {σ r : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (hr : 0 < r) (hr1 : r ≤ 1) :
    diniTransform (fun s => s^σ) r ≤ diniPowerConstant σ * r^σ := by
  have hu : 0 ≤ min (2*r) 1 := le_min (by positivity) zero_le_one
  have hnear : (min (2*r) 1)^σ/σ ≤ (2:ℝ)^σ/σ*r^σ := by
    calc
      _ ≤ (2*r)^σ/σ := div_le_div_of_nonneg_right
        (Real.rpow_le_rpow hu (min_le_left _ _) hσ0.le) hσ0.le
      _ = _ := by rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hr.le]; ring
  have hrpow : r ≤ r^σ := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hr hr1 hσ1.le
  have hid : r * r^(σ-1) = r^σ := by
    rw [Real.rpow_sub hr, Real.rpow_one]
    field_simp
  have hfar : r*((r^(σ-1)-1)/(1-σ)) ≤ r^σ/(1-σ) := by
    apply (le_div_iff₀ (by linarith : 0 < 1-σ)).2
    field_simp
    nlinarith
  unfold diniTransform
  dsimp only
  rw [diniPower_near_integral hσ0 hσ1 hu, diniPower_far_integral hσ1 hr hr1, Real.one_rpow]
  unfold diniPowerConstant
  simp only [div_eq_mul_inv] at hnear hfar ⊢
  nlinarith [Real.rpow_pos_of_pos hr σ]

theorem diniIntegrable_of_powerBound {η B r : ℝ} {φ : ℝ → ℝ}
    (hη0 : 0 < η) (hη1 : η < 1) (_hB : 0 ≤ B) (hφ : Measurable φ)
    (hb : powerBound η B φ) (hr : 0 < r) (hr1 : r ≤ 1) : diniIntegrable φ r := by
  have hu : 0 ≤ min (2*r) 1 := le_min (by positivity) zero_le_one
  constructor
  · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hu]
    have hg := ((intervalIntegral.intervalIntegrable_rpow'
      (a := 0) (b := min (2*r) 1) (by linarith : -1 < η-1)).const_mul B).1
    refine hg.mono' (hφ.div measurable_id).aestronglyMeasurable.restrict ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have hs1 : s ≤ 1 := hs.2.trans (min_le_right _ _)
    have hb' := hb s ⟨hs.1,hs1⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hb'.1 hs.1.le)]
    calc
      _ ≤ (B*s^η)/s := div_le_div_of_nonneg_right hb'.2 hs.1.le
      _ = B*s^(η-1) := by rw [mul_div_assoc, power_div_self_eq hs.1.le hη1.ne]
  · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hr1]
    have hn : (0 : ℝ) ∉ Set.uIcc r 1 := by simp [Set.uIcc_of_le hr1,hr.not_ge]
    have hg := ((intervalIntegral.intervalIntegrable_rpow
      (μ := volume) (r := η-2) (Or.inr hn)).const_mul B).1
    refine hg.mono' (hφ.div (measurable_id.pow_const 2)).aestronglyMeasurable.restrict ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have hs0 : 0 < s := hr.trans hs.1
    have hb' := hb s ⟨hs0,hs.2⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hb'.1 (sq_nonneg _))]
    calc
      _ ≤ (B*s^η)/s^2 := div_le_div_of_nonneg_right hb'.2 (sq_nonneg _)
      _ = B*s^(η-2) := by rw [mul_div_assoc, power_div_sq_eq hs0.le (by linarith : η ≠ 2)]

theorem diniTransform_mono {φ ψ : ℝ → ℝ} {r : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) (hφ : diniIntegrable φ r) (hψ : diniIntegrable ψ r)
    (h : ∀ s ∈ Set.Ioc (0 : ℝ) 1, φ s ≤ ψ s) : diniTransform φ r ≤ diniTransform ψ r := by
  have hu : 0 ≤ min (2*r) 1 := le_min (by positivity) zero_le_one
  have hn := intervalIntegral.integral_mono_on_of_le_Ioo hu hφ.1 hψ.1
    (fun s hs => div_le_div_of_nonneg_right (h s ⟨hs.1,hs.2.le.trans (min_le_right _ _)⟩) hs.1.le)
  have hf := intervalIntegral.integral_mono_on_of_le_Ioo hr1 hφ.2 hψ.2
    (fun s hs => div_le_div_of_nonneg_right (h s ⟨hr.trans hs.1,hs.2.le⟩) (sq_nonneg _))
  unfold diniTransform
  linarith [h r ⟨hr,hr1⟩,h 1 ⟨zero_lt_one,le_rfl⟩,
    mul_le_mul_of_nonneg_left hf hr.le,
    mul_le_mul_of_nonneg_left (h 1 ⟨zero_lt_one,le_rfl⟩) hr.le]

theorem diniTransform_add {φ ψ : ℝ → ℝ} {r : ℝ}
    (hφ : diniIntegrable φ r) (hψ : diniIntegrable ψ r) :
    diniTransform (φ+ψ) r = diniTransform φ r + diniTransform ψ r := by
  unfold diniTransform
  simp only [Pi.add_apply, add_div]
  rw [intervalIntegral.integral_add hφ.1 hψ.1, intervalIntegral.integral_add hφ.2 hψ.2]
  ring

theorem diniTransform_const_mul (a : ℝ) (φ : ℝ → ℝ) (r : ℝ) :
    diniTransform (fun s => a*φ s) r = a*diniTransform φ r := by
  unfold diniTransform
  simp only [mul_div_assoc, intervalIntegral.integral_const_mul]
  ring

theorem diniIntegrable_const_mul {φ : ℝ → ℝ} {r : ℝ} (hφ : diniIntegrable φ r) (a : ℝ) :
    diniIntegrable (fun s => a*φ s) r := by
  constructor <;> simpa only [mul_div_assoc] using
    (show IntervalIntegrable _ _ _ _ from (by first | exact hφ.1.const_mul a | exact hφ.2.const_mul a))

theorem diniIntegrable_add {φ ψ : ℝ → ℝ} {r : ℝ}
    (hφ : diniIntegrable φ r) (hψ : diniIntegrable ψ r) : diniIntegrable (φ+ψ) r := by
  exact ⟨by simpa only [Pi.add_apply,add_div] using hφ.1.add hψ.1,
    by simpa only [Pi.add_apply,add_div] using hφ.2.add hψ.2⟩

theorem diniTransform_two_power_le {φ : ℝ → ℝ} {r γ η a b : ℝ}
    (hγ0 : 0 < γ) (hγ1 : γ < 1) (hη0 : 0 < η) (hη1 : η < 1)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hr : 0 < r) (hr1 : r ≤ 1)
    (hi : diniIntegrable φ r)
    (hφ : ∀ s ∈ Set.Ioc (0 : ℝ) 1, φ s ≤ a*s^γ+b*s^η) :
    diniTransform φ r ≤ a*diniPowerConstant γ*r^γ+b*diniPowerConstant η*r^η := by
  have hu : 0 ≤ min (2*r) 1 := le_min (by positivity) zero_le_one
  have hiγ : diniIntegrable (fun s => s^γ) r :=
    ⟨diniPower_near_integrable hγ0 hγ1 hu,diniPower_far_integrable hγ1 hr hr1⟩
  have hiη : diniIntegrable (fun s => s^η) r :=
    ⟨diniPower_near_integrable hη0 hη1 hu,diniPower_far_integrable hη1 hr hr1⟩
  let f : ℝ → ℝ := fun s => a*s^γ
  let g : ℝ → ℝ := fun s => b*s^η
  have hif : diniIntegrable f r := diniIntegrable_const_mul hiγ a
  have hig : diniIntegrable g r := diniIntegrable_const_mul hiη b
  calc
    _ ≤ diniTransform (f+g) r := diniTransform_mono hr hr1 hi
      (diniIntegrable_add hif hig) hφ
    _ = a*diniTransform (fun s => s^γ) r+b*diniTransform (fun s => s^η) r := by
      rw [diniTransform_add hif hig]
      exact congrArg₂ (·+·) (diniTransform_const_mul a _ _) (diniTransform_const_mul b _ _)
    _ ≤ _ := by
      have hcγ := mul_le_mul_of_nonneg_left (diniTransform_power_le hγ0 hγ1 hr hr1) ha
      have hcη := mul_le_mul_of_nonneg_left (diniTransform_power_le hη0 hη1 hr hr1) hb
      nlinarith

/-- Positive-kernel iteration reaches the sharp exponent without assuming
that the sharp Hölder seminorm is finite. The sole a priori modulus is η. -/
theorem dini_iteration {φ : ℝ → ℝ} {η γ A B δ : ℝ}
    (hη0 : 0 < η) (hη1 : η < 1) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hδ : 0 ≤ δ) (hm : Measurable φ)
    (hcoarse : powerBound η B φ)
    (hineq : ∀ r ∈ Set.Ioc (0 : ℝ) 1,
      φ r ≤ A*r^γ+δ*diniTransform φ r)
    (hsmallγ : δ*diniPowerConstant γ ≤ 1/2)
    (hsmallη : δ*diniPowerConstant η ≤ 1/2) : powerBound γ (2*A) φ := by
  have hkη : 0 ≤ diniPowerConstant η := by
    unfold diniPowerConstant
    positivity
  have hq0 : 0 ≤ δ*diniPowerConstant η := mul_nonneg hδ hkη
  have hfinite (N : ℕ) : ∀ r ∈ Set.Ioc (0 : ℝ) 1,
      φ r ≤ 2*A*r^γ+B*(δ*diniPowerConstant η)^N*r^η := by
    induction N with
    | zero =>
      intro r hr
      have hc := (hcoarse r hr).2
      simpa only [pow_zero,mul_one] using
        hc.trans (le_add_of_nonneg_left
          (mul_nonneg (by positivity : 0 ≤ 2*A) (Real.rpow_nonneg hr.1.le γ)))
    | succ N ih =>
      intro r hr
      have hi := diniIntegrable_of_powerBound hη0 hη1 hB hm hcoarse hr.1 hr.2
      have hd := diniTransform_two_power_le hγ0 hγ1 hη0 hη1
        (by positivity : 0 ≤ 2*A) (by positivity : 0 ≤ B*(δ*diniPowerConstant η)^N)
        hr.1 hr.2 hi ih
      have hd' := mul_le_mul_of_nonneg_left hd hδ
      have hg := mul_le_mul_of_nonneg_right hsmallγ
        (mul_nonneg (by positivity : 0 ≤ 2*A) (Real.rpow_nonneg hr.1.le γ))
      have hi' := hineq r hr
      rw [pow_succ]
      nlinarith
  intro r hr
  refine ⟨(hcoarse r hr).1,?_⟩
  have hlim : Tendsto (fun N : ℕ => 2*A*r^γ+B*(δ*diniPowerConstant η)^N*r^η)
      atTop (𝓝 (2*A*r^γ)) := by
    have hp := tendsto_pow_atTop_nhds_zero_of_lt_one hq0
      (lt_of_le_of_lt hsmallη (by norm_num : (1/2 : ℝ) < 1))
    simpa using ((hp.const_mul B).mul_const (r^η)).const_add (2*A*r^γ)
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hlim
    (Filter.Eventually.of_forall fun N => hfinite N r hr)

end Yau.LeafProofs.L05Aux
