import Yau.LeafProofs.L05DiniKernelSliceBounds
import Yau.LeafProofs.L05DiniKernelCausalIntervals

noncomputable section

open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic
open L16Aux

local instance l05DiniKernelSpatialDualGroup (n : ℕ) : NormedAddCommGroup (Space n →L[ℝ] ℝ) := inferInstance
local instance l05DiniKernelSpatialDualSpace (n : ℕ) : NormedSpace ℝ (Space n →L[ℝ] ℝ) := inferInstance
local instance l05DiniKernelSpatialHessianGroup (n : ℕ) : NormedAddCommGroup (DiniHessian n) := inferInstance
local instance l05DiniKernelSpatialHessianSpace (n : ℕ) : NormedSpace ℝ (DiniHessian n) := inferInstance

theorem dini_modulus_power_norm_le {n : ℕ} {psi : ℝ → ℝ} {eta B : ℝ}
    (he : 0 < eta) (hz : psi 0=0) (hp : ∀ s : ℝ, 0 < s → psi s ≤ B*s^eta)
    (y : Space n) : psi ‖y‖ ≤ B*‖y‖^eta := by
  rcases (norm_nonneg y).eq_or_lt with h | h
  · rw [← h,hz,Real.zero_rpow he.ne',mul_zero]
  · exact hp _ h

theorem heatDuhamel_spatial_dini_bound {n : ℕ} :
    ∃ C : ℝ, 0 < C ∧ ∀ (eta B M : ℝ) (g : Point n → ℝ) (psi : ℝ → ℝ),
      0 < eta → eta < 1 → 0 ≤ B → Continuous g → (∀ p, |g p| ≤ M) →
      Measurable psi → psi 0=0 → MonotoneOn psi (Set.Ioi (0:ℝ)) →
      (∀ s : ℝ, 0 < s → 0 ≤ psi s ∧ psi s ≤ B*s^eta) →
      (∀ s : ℝ, ∀ x y : Space n, |g (x,s)-g (y,s)| ≤ psi ‖x-y‖) →
      ∀ t : ℝ, 0 ≤ t → ∀ r : ℝ, 0 < r → ∀ x h : Space n, ‖h‖ ≤ r →
        ‖fderiv ℝ (fderiv ℝ (heatDuhamel g t)) (x+h)-
          fderiv ℝ (fderiv ℝ (heatDuhamel g t)) x‖ ≤ C*diniBudget psi r := by
  obtain ⟨C2,hC2,hRecent⟩ := diniHeatD2_recent_integral (n := n)
  obtain ⟨C3,hC3,hOld⟩ := diniHeatD2_old_space_integral (n := n)
  obtain ⟨M2,hM2,hWeight⟩ := diniHeatD2_weighted (n := n)
  obtain ⟨M3,hM3,hShift⟩ := diniHeatD2_shift_weighted (n := n)
  refine ⟨2*C2+C3,by positivity,?_⟩
  intro eta B M g psi he he1 hB hg hM hm hz hmono hp hmod t ht r hr x h hh
  have hBudget := diniBudget_nonneg hr (fun s hs => (hp s hs).1)
  rcases ht.eq_or_lt with hzero | ht
  · have htzero : t=0 := hzero.symm
    subst t
    have hz0 : heatDuhamel g 0 = fun _ : Space n => (0:ℝ) := funext (heatDuhamel_zero g)
    have hd0 : fderiv ℝ (heatDuhamel g 0)=fun _ : Space n => (0 : Space n →L[ℝ] ℝ) := by
      rw [hz0,fderiv_fun_const]
      rfl
    simp only [hd0,fderiv_const_apply,sub_self,norm_zero]
    positivity
  have hH (s : ℝ) (x y : Space n) : |g (x,s)-g (y,s)| ≤ B*‖x-y‖^eta :=
    (hmod s x y).trans (dini_modulus_power_norm_le he hz (fun a ha => (hp a ha).2) (x-y))
  have hgc (s : ℝ) : Continuous (fun y : Space n => g (y,s)) :=
    hg.comp (continuous_id.prodMk continuous_const)
  have hMs (s : ℝ) (y : Space n) : |g (y,s)| ≤ M := hM (y,s)
  let J : ℝ → ℝ := fun a => ∫ y : Space n, ‖diniHeatD2 a y‖*psi ‖y‖
  let K : ℝ → ℝ := fun a => ∫ y : Space n, ‖diniHeatD2 a (y+h)-diniHeatD2 a y‖*psi ‖y‖
  have hRec := hRecent eta B r psi he he1 hB hr hm hz hmono hp
  have hOldData := hOld eta B r psi h he he1 hB hr hh hm hz hmono hp
  have hJI : IntervalIntegrable J volume 0 (r^2) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (sq_nonneg r)).mpr hRec.1.integral_prod_left
  have hKI : IntegrableOn K (Set.Ioi (r^2)) := hOldData.1.integral_prod_left
  have hJpos (a : ℝ) : 0 ≤ J a := integral_nonneg (fun y => mul_nonneg (norm_nonneg _)
    (dini_modulus_nonneg_norm hz (fun s hs => (hp s hs).1) y))
  have hKpos (a : ℝ) : 0 ≤ K a := integral_nonneg (fun y => mul_nonneg (norm_nonneg _)
    (dini_modulus_nonneg_norm hz (fun s hs => (hp s hs).1) y))
  let A : ℝ → DiniHessian n := fun s =>
    fderiv ℝ (fderiv ℝ (heatAverage (t-s) (fun y => g (y,s)))) (x+h)-
      fderiv ℝ (fderiv ℝ (heatAverage (t-s) (fun y => g (y,s)))) x
  let V : ℝ → DiniHessian n := fun a =>
    fderiv ℝ (fderiv ℝ (heatAverage a (fun y => g (y,t-a)))) (x+h)-
      fderiv ℝ (fderiv ℝ (heatAverage a (fun y => g (y,t-a)))) x
  have hIplus := heatAverage_secondFDeriv_time_integrable he hg hM hB hH ht (x+h)
  have hIx := heatAverage_secondFDeriv_time_integrable he hg hM hB hH ht x
  have hAI : IntervalIntegrable A volume 0 t := hIplus.sub hIx
  have hVI : IntervalIntegrable V volume 0 t := by
    simpa only [V,A,sub_self,sub_zero,sub_sub_cancel] using (hAI.comp_sub_left t).symm
  have heq : fderiv ℝ (fderiv ℝ (heatDuhamel g t)) (x+h)-
      fderiv ℝ (fderiv ℝ (heatDuhamel g t)) x = ∫ a in (0:ℝ)..t, V a := by
    rw [(heatDuhamel_fderiv_hasFDerivAt he hg hM hB hH ht (x+h)).fderiv,
      (heatDuhamel_fderiv_hasFDerivAt he hg hM hB hH ht x).fderiv,
      ← intervalIntegral.integral_sub hIplus hIx]
    simpa only [V,A,sub_self,sub_zero,sub_sub_cancel] using
      (intervalIntegral.integral_comp_sub_left (a := (0:ℝ)) (b := t) A t).symm
  have hnear (a : ℝ) (ha : a ∈ Set.Ioc 0 t) : ‖V a‖ ≤ 2*J a := by
    have hI := (hWeight eta B psi he he1 hB hm hz hmono hp a ha.1).1
    have h1 := dini_heatAverage_hessian_norm_le ha.1 (hgc (t-a)) (hMs (t-a)) hI (hmod (t-a)) (x+h)
    have h2 := dini_heatAverage_hessian_norm_le ha.1 (hgc (t-a)) (hMs (t-a)) hI (hmod (t-a)) x
    exact (norm_sub_le _ _).trans (by change _ ≤ 2*J a; linarith only [h1,h2])
  have hfar (a : ℝ) (ha : a ∈ Set.Ioc (r^2) t) : ‖V a‖ ≤ K a := by
    have hgeo := dini_old_age_geometry hr ha.1
    have hI := (hShift eta B psi he he1 hB hm hz hmono hp a hgeo.1 h (hh.trans hgeo.2)).1
    exact dini_heatAverage_spatial_increment_norm_le hgeo.1 (hgc (t-a)) (hMs (t-a)) x h hI (hmod (t-a))
  have hJA : (∫ a in (0:ℝ)..r^2, 2*J a) ≤ (2*C2)*diniBudget psi r := by
    rw [intervalIntegral.integral_const_mul]
    convert! mul_le_mul_of_nonneg_left hRec.2 (by norm_num : (0:ℝ) ≤ 2) using 1 <;> ring
  rw [heq]
  have hb := dini_near_far_integral_bound (sq_pos_of_pos hr) ht.le
    (mul_nonneg hC3.le hBudget) hVI (hJI.const_mul 2) hKI
    (fun a ha => mul_nonneg (by norm_num) (hJpos a)) (fun a ha => hKpos a)
    hnear hfar hJA hOldData.2
  convert! hb using 1 <;> ring

end Yau.LeafProofs.L05Aux
