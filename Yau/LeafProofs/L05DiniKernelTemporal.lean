import Yau.LeafProofs.L05DiniKernelSpatial

noncomputable section

open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic
open L16Aux

local instance l05DiniKernelTemporalDualGroup (n : ℕ) : NormedAddCommGroup (Space n →L[ℝ] ℝ) := inferInstance
local instance l05DiniKernelTemporalDualSpace (n : ℕ) : NormedSpace ℝ (Space n →L[ℝ] ℝ) := inferInstance
local instance l05DiniKernelTemporalHessianGroup (n : ℕ) : NormedAddCommGroup (DiniHessian n) := inferInstance
local instance l05DiniKernelTemporalHessianSpace (n : ℕ) : NormedSpace ℝ (DiniHessian n) := inferInstance

theorem dini_heatDuhamel_hessian_eq_integral {n : ℕ} {eta M B t : ℝ} {g : Point n → ℝ}
    (he : 0 < eta) (hg : Continuous g) (hM : ∀ p, |g p| ≤ M) (hB : 0 ≤ B)
    (hH : ∀ s x y, |g (x,s)-g (y,s)| ≤ B*‖x-y‖^eta) (ht : 0 ≤ t) (x : Space n) :
    fderiv ℝ (fderiv ℝ (heatDuhamel g t)) x =
      ∫ s in (0:ℝ)..t, fderiv ℝ (fderiv ℝ (heatAverage (t-s) (fun y => g (y,s)))) x := by
  rcases ht.eq_or_lt with hzero | ht
  · have htzero : t=0 := hzero.symm
    subst t
    have hz : heatDuhamel g 0=fun _ : Space n => (0:ℝ) := funext (heatDuhamel_zero g)
    simp only [hz,fderiv_fun_const,intervalIntegral.integral_same]
    exact fderiv_const_apply (0 : Space n →L[ℝ] ℝ)
  · exact (heatDuhamel_fderiv_hasFDerivAt he hg hM hB hH ht x).fderiv

theorem dini_heatAverage_time_integrable_nonneg {n : ℕ} {eta M B t : ℝ} {g : Point n → ℝ}
    (he : 0 < eta) (hg : Continuous g) (hM : ∀ p, |g p| ≤ M) (hB : 0 ≤ B)
    (hH : ∀ s x y, |g (x,s)-g (y,s)| ≤ B*‖x-y‖^eta) (ht : 0 ≤ t) (x : Space n) :
    IntervalIntegrable (fun s : ℝ => fderiv ℝ (fderiv ℝ (heatAverage (t-s) (fun y => g (y,s)))) x)
      volume 0 t := by
  rcases ht.eq_or_lt with hzero | ht
  · have htzero : t=0 := hzero.symm
    subst t
    exact IntervalIntegrable.refl
  · exact heatAverage_secondFDeriv_time_integrable he hg hM hB hH ht x

theorem heatDuhamel_temporal_dini_bound {n : ℕ} :
    ∃ C : ℝ, 0 < C ∧ ∀ (eta B M : ℝ) (g : Point n → ℝ) (psi : ℝ → ℝ),
      0 < eta → eta < 1 → 0 ≤ B → Continuous g → (∀ p, |g p| ≤ M) →
      Measurable psi → psi 0=0 → MonotoneOn psi (Set.Ioi (0:ℝ)) →
      (∀ a : ℝ, 0 < a → 0 ≤ psi a ∧ psi a ≤ B*a^eta) →
      (∀ a : ℝ, ∀ x y : Space n, |g (x,a)-g (y,a)| ≤ psi ‖x-y‖) →
      ∀ s t r : ℝ, 0 ≤ s → s ≤ t → 0 < r → t-s ≤ r^2 → ∀ x : Space n,
        ‖fderiv ℝ (fderiv ℝ (heatDuhamel g t)) x-
          fderiv ℝ (fderiv ℝ (heatDuhamel g s)) x‖ ≤ C*diniBudget psi r := by
  obtain ⟨C2,hC2,hRecent⟩ := diniHeatD2_recent_integral (n := n)
  obtain ⟨C4,hC4,hOld⟩ := diniHeatD2_old_time_integral (n := n)
  obtain ⟨M2,hM2,hWeight⟩ := diniHeatD2_weighted (n := n)
  obtain ⟨M4,hM4,hTime⟩ := diniHeatD2_time_weighted (n := n)
  refine ⟨4*C2+C4,by positivity,?_⟩
  intro eta B M g psi he he1 hB hg hM hm hz hmono hp hmod s t r hs hst hr hdelta x
  have hH (a : ℝ) (x y : Space n) : |g (x,a)-g (y,a)| ≤ B*‖x-y‖^eta :=
    (hmod a x y).trans (dini_modulus_power_norm_le he hz (fun a ha => (hp a ha).2) (x-y))
  have hgc (a : ℝ) : Continuous (fun y : Space n => g (y,a)) :=
    hg.comp (continuous_id.prodMk continuous_const)
  have hMs (a : ℝ) (y : Space n) : |g (y,a)| ≤ M := hM (y,a)
  let J : ℝ → ℝ := fun a => ∫ y : Space n, ‖diniHeatD2 a y‖*psi ‖y‖
  let K : ℝ → ℝ := fun a => ∫ y : Space n, ‖diniHeatD2 (a+(t-s)) y-diniHeatD2 a y‖*psi ‖y‖
  have hRec := hRecent eta B (2*r) psi he he1 hB (by positivity) hm hz hmono hp
  have hOldData := hOld eta B r (t-s) psi he he1 hB hr (sub_nonneg.mpr hst) hdelta hm hz hmono hp
  have hJI : IntervalIntegrable J volume 0 ((2*r)^2) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (sq_nonneg (2*r))).mpr hRec.1.integral_prod_left
  have hKI : IntegrableOn K (Set.Ioi (r^2)) := hOldData.1.integral_prod_left
  have hJpos (a : ℝ) : 0 ≤ J a := integral_nonneg (fun y => mul_nonneg (norm_nonneg _)
    (dini_modulus_nonneg_norm hz (fun a ha => (hp a ha).1) y))
  have hKpos (a : ℝ) : 0 ≤ K a := integral_nonneg (fun y => mul_nonneg (norm_nonneg _)
    (dini_modulus_nonneg_norm hz (fun a ha => (hp a ha).1) y))
  have hRecBound (q U : ℝ) (hU : 0 ≤ U) (hUR : U ≤ (2*r)^2) :
      ‖∫ a in (0:ℝ)..U, fderiv ℝ (fderiv ℝ (heatAverage a (fun y => g (y,q-a)))) x‖ ≤
        (2*C2)*diniBudget psi r := by
    have hb := dini_interval_norm_le_recent le_rfl hU hUR hJI (fun a ha => hJpos a)
      (ae_of_all _ (fun a ha => dini_heatAverage_hessian_norm_le ha.1 (hgc (q-a)) (hMs (q-a))
        (hWeight eta B psi he he1 hB hm hz hmono hp a ha.1).1 (hmod (q-a)) x))
    have hD := diniBudget_dilate_le he he1 hB hm hp hr (by norm_num : (1:ℝ) ≤ 2)
    calc
      _ ≤ ∫ a in (0:ℝ)..(2*r)^2, J a := hb
      _ ≤ C2*diniBudget psi (2*r) := hRec.2
      _ ≤ C2*(2*diniBudget psi r) := mul_le_mul_of_nonneg_left hD hC2.le
      _ = _ := by ring
  let b : ℝ := max 0 (s-r^2)
  have hgeo := dini_causal_time_geometry hs hst hdelta
  have hb : 0 ≤ b := hgeo.1
  have hbs : b ≤ s := hgeo.2.1
  have hbt : b ≤ t := hgeo.2.2.1
  let N : ℝ → DiniHessian n := fun a => fderiv ℝ (fderiv ℝ (heatAverage (t-a) (fun y => g (y,a)))) x
  let O : ℝ → DiniHessian n := fun a => fderiv ℝ (fderiv ℝ (heatAverage (s-a) (fun y => g (y,a)))) x
  have hNI : IntervalIntegrable N volume 0 t := dini_heatAverage_time_integrable_nonneg he hg hM hB hH (hs.trans hst) x
  have hOI : IntervalIntegrable O volume 0 s := dini_heatAverage_time_integrable_nonneg he hg hM hB hH hs x
  have hEqN : (∫ a in b..t, N a)=
      ∫ a in (0:ℝ)..t-b, fderiv ℝ (fderiv ℝ (heatAverage a (fun y => g (y,t-a)))) x := by
    simpa only [N,sub_sub_cancel,sub_self] using
      (intervalIntegral.integral_comp_sub_left (a := b) (b := t)
        (fun a : ℝ => fderiv ℝ (fderiv ℝ (heatAverage a (fun y => g (y,t-a)))) x) t)
  have hEqO : (∫ a in b..s, O a)=
      ∫ a in (0:ℝ)..s-b, fderiv ℝ (fderiv ℝ (heatAverage a (fun y => g (y,s-a)))) x := by
    simpa only [O,sub_sub_cancel,sub_self] using
      (intervalIntegral.integral_comp_sub_left (a := b) (b := s)
        (fun a : ℝ => fderiv ℝ (fderiv ℝ (heatAverage a (fun y => g (y,s-a)))) x) s)
  have hNew : ‖∫ a in b..t, N a‖ ≤ (2*C2)*diniBudget psi r := by
    rw [hEqN]
    exact hRecBound t (t-b) (sub_nonneg.mpr hbt) (by nlinarith only [hgeo.2.2.2.1,sq_nonneg r])
  have hRecentOld : ‖∫ a in b..s, O a‖ ≤ (2*C2)*diniBudget psi r := by
    rw [hEqO]
    exact hRecBound s (s-b) (sub_nonneg.mpr hbs) (by nlinarith only [hgeo.2.2.2.2.1,sq_nonneg r])
  have hOldBound : ‖∫ a in (0:ℝ)..b, N a-O a‖ ≤ C4*diniBudget psi r := by
    by_cases hb0 : b=0
    · rw [hb0,intervalIntegral.integral_same,norm_zero]
      exact mul_nonneg hC4.le (diniBudget_nonneg hr (fun a ha => (hp a ha).1))
    have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
    have hsb : s-b=r^2 := hgeo.2.2.2.2.2 hbpos
    let V : ℝ → DiniHessian n := fun a =>
      fderiv ℝ (fderiv ℝ (heatAverage (a+(t-s)) (fun y => g (y,s-a)))) x-
        fderiv ℝ (fderiv ℝ (heatAverage a (fun y => g (y,s-a)))) x
    have harg (a : ℝ) : s-a+(t-s)=t-a := by ring
    have hEq : (∫ a in (0:ℝ)..b, N a-O a)=∫ a in s-b..s, V a := by
      simpa only [N,O,V,sub_sub_cancel,sub_zero,harg] using
        (intervalIntegral.integral_comp_sub_left (a := (0:ℝ)) (b := b) V s)
    rw [hEq]
    apply (dini_interval_norm_le_tail (F := V) (le_of_eq hsb.symm) (sub_le_self s hb) hKI
      (fun a ha => hKpos a) ?_).trans hOldData.2
    apply ae_of_all
    intro a ha
    have ha0 : 0 < a := (sq_pos_of_pos hr).trans (hsb ▸ ha.1)
    exact dini_heatAverage_time_increment_norm_le ha0 (sub_nonneg.mpr hst) (hgc (s-a)) (hMs (s-a)) x
      (hTime eta B psi he he1 hB hm hz hmono hp a ha0 (t-s) (sub_nonneg.mpr hst)).1 (hmod (s-a))
  rw [dini_heatDuhamel_hessian_eq_integral he hg hM hB hH (hs.trans hst) x,
    dini_heatDuhamel_hessian_eq_integral he hg hM hB hH hs x]
  change ‖(∫ a in (0:ℝ)..t, N a)-(∫ a in (0:ℝ)..s, O a)‖ ≤ _
  rw [dini_causal_interval_decomposition hb hbs hst hNI hOI]
  have hn : ‖(∫ a in (0:ℝ)..b, N a-O a)+(∫ a in b..t, N a)-(∫ a in b..s, O a)‖ ≤
      ‖∫ a in (0:ℝ)..b, N a-O a‖+‖∫ a in b..t, N a‖+‖∫ a in b..s, O a‖ :=
    (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
  exact hn.trans (by nlinarith only [hOldBound,hNew,hRecentOld])

end Yau.LeafProofs.L05Aux
