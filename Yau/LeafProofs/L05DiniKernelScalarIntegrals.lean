import Yau.LeafProofs.L05DiniKernelChangeVariables

noncomputable section

open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.LeafProofs.L05Aux

theorem dini_recent_transformed_integrand {c s : ℝ} (hc : 0 < c) (hs : 0 < s) (psi : ℝ → ℝ) :
    |2*s/c^2| • (((s/c)^2)⁻¹*psi (c*Real.sqrt ((s/c)^2)))=2*(psi s/s) := by
  have hsq : Real.sqrt ((s/c)^2)=s/c := by
    rw [Real.sqrt_sq_eq_abs,abs_of_pos (div_pos hs hc)]
  have he : c*Real.sqrt ((s/c)^2)=s := by rw [hsq]; field_simp
  rw [abs_of_nonneg (div_nonneg (mul_nonneg (by norm_num) hs.le) (sq_nonneg c)),smul_eq_mul,he]
  field_simp [hc.ne',hs.ne']

theorem dini_recent_scalar_data {psi : ℝ → ℝ} {eta B c R : ℝ}
    (he : 0 < eta) (he1 : eta < 1) (hB : 0 ≤ B) (hm : Measurable psi)
    (hpsi : ∀ s : ℝ, 0 < s → 0 ≤ psi s ∧ psi s ≤ B*s^eta) (hc : 0 < c) (hR : 0 < R) :
    IntervalIntegrable (fun a : ℝ => a⁻¹*psi (c*Real.sqrt a)) volume 0 (R^2) ∧
      (∫ a in (0:ℝ)..R^2, a⁻¹*psi (c*Real.sqrt a))=2*(∫ s in (0:ℝ)..c*R, psi s/s) := by
  let f := fun s : ℝ => (s/c)^2
  let g := fun a : ℝ => a⁻¹*psi (c*Real.sqrt a)
  let S := Set.Ioc (0:ℝ) (c*R)
  have hcR : 0 < c*R := mul_pos hc hR
  have hf (s : ℝ) (hs : s ∈ S) : HasDerivWithinAt f (2*s/c^2) S s :=
    (dini_square_div_hasDerivAt hc s).hasDerivWithinAt
  have hinj : Set.InjOn f S := (dini_square_div_strictMonoOn hc).injOn.mono (fun s hs => hs.1)
  have himage : f '' S=Set.Ioc (0:ℝ) (R^2) := dini_square_div_recent_image hc hR
  have hchange := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioc hf hinj g
  have hNear := (diniBudget_integrable he he1 hB hm hpsi hcR).1
  have hTrans : IntegrableOn (fun s : ℝ => |2*s/c^2| • g (f s)) S := by
    apply (hNear.1.const_mul 2).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact (dini_recent_transformed_integrand hc hs.1 psi).symm
  have hSource := (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioc hf hinj g).mpr hTrans
  rw [himage] at hSource hchange
  refine ⟨?_,?_⟩
  · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (sq_nonneg R)]
    exact hSource
  · calc
      _=(∫ a in Set.Ioc (0:ℝ) (R^2), g a) := intervalIntegral.integral_of_le (sq_nonneg R)
      _=(∫ s in S, 2*(psi s/s)) := hchange.trans
        (setIntegral_congr_fun measurableSet_Ioc (fun s hs => dini_recent_transformed_integrand hc hs.1 psi))
      _=2*(∫ s in (0:ℝ)..c*R, psi s/s) := by
        rw [integral_const_mul,intervalIntegral.integral_of_le hcR.le]

theorem dini_recent_scalar_change {psi : ℝ → ℝ} {eta B c R : ℝ}
    (he : 0 < eta) (he1 : eta < 1) (hB : 0 ≤ B) (hm : Measurable psi)
    (hpsi : ∀ s : ℝ, 0 < s → 0 ≤ psi s ∧ psi s ≤ B*s^eta) (hc : 0 < c) (hR : 0 < R) :
    (∫ a in (0:ℝ)..R^2, a⁻¹*psi (c*Real.sqrt a))=2*(∫ s in (0:ℝ)..c*R, psi s/s) :=
  (dini_recent_scalar_data he he1 hB hm hpsi hc hR).2

theorem dini_old_transformed_integrand {c s : ℝ} (hc : 0 < c) (hs : 0 < s) (psi : ℝ → ℝ) :
    |2*s/c^2| • (((s/c)^2)^(-(3/2:ℝ))*psi (c*Real.sqrt ((s/c)^2)))=(2*c)*(psi s/s^2) := by
  have hdiv : 0 < s/c := div_pos hs hc
  have hsq : Real.sqrt ((s/c)^2)=s/c := by rw [Real.sqrt_sq_eq_abs,abs_of_pos hdiv]
  have he : c*Real.sqrt ((s/c)^2)=s := by rw [hsq]; field_simp
  have hpower : ((s/c)^2)^(-(3/2:ℝ))=((s/c)^3)⁻¹ := by
    calc
      _=((s/c)^(2:ℝ))^(-(3/2:ℝ)) := by rw [Real.rpow_two]
      _=(s/c)^((2:ℝ)*(-(3/2:ℝ))) := (Real.rpow_mul hdiv.le _ _).symm
      _=(s/c)^(-(3:ℝ)) := by congr 1; ring
      _=_ := by rw [Real.rpow_neg hdiv.le]; norm_num [Real.rpow_natCast]
  rw [abs_of_nonneg (div_nonneg (mul_nonneg (by norm_num) hs.le) (sq_nonneg c)),smul_eq_mul,he,hpower]
  field_simp [hc.ne',hs.ne'] <;> ring

theorem dini_old_scalar_data {psi : ℝ → ℝ} {eta B c R : ℝ}
    (he : 0 < eta) (he1 : eta < 1) (hB : 0 ≤ B) (hm : Measurable psi)
    (hpsi : ∀ s : ℝ, 0 < s → 0 ≤ psi s ∧ psi s ≤ B*s^eta) (hc : 0 < c) (hR : 0 < R) :
    IntegrableOn (fun a : ℝ => a^(-(3/2:ℝ))*psi (c*Real.sqrt a)) (Set.Ioi (R^2)) ∧
      (∫ a in Set.Ioi (R^2), a^(-(3/2:ℝ))*psi (c*Real.sqrt a))=
        2*c*(∫ s in Set.Ioi (c*R), psi s/s^2) := by
  let f := fun s : ℝ => (s/c)^2
  let g := fun a : ℝ => a^(-(3/2:ℝ))*psi (c*Real.sqrt a)
  let S := Set.Ioi (c*R)
  have hcR : 0 < c*R := mul_pos hc hR
  have hf (s : ℝ) (hs : s ∈ S) : HasDerivWithinAt f (2*s/c^2) S s :=
    (dini_square_div_hasDerivAt hc s).hasDerivWithinAt
  have hinj : Set.InjOn f S := (dini_square_div_strictMonoOn hc).injOn.mono (fun s hs => hcR.trans hs)
  have himage : f '' S=Set.Ioi (R^2) := dini_square_div_old_image hc hR
  have hchange := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hf hinj g
  have hFar := (diniBudget_integrable he he1 hB hm hpsi hcR).2
  have hTrans : IntegrableOn (fun s : ℝ => |2*s/c^2| • g (f s)) S := by
    apply (hFar.const_mul (2*c)).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact (dini_old_transformed_integrand hc (hcR.trans hs) psi).symm
  have hSource := (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hf hinj g).mpr hTrans
  rw [himage] at hSource hchange
  refine ⟨hSource,?_⟩
  calc
    _=(∫ s in S, (2*c)*(psi s/s^2)) := hchange.trans
      (setIntegral_congr_fun measurableSet_Ioi (fun s hs => dini_old_transformed_integrand hc (hcR.trans hs) psi))
    _=(2*c)*(∫ s in Set.Ioi (c*R), psi s/s^2) := integral_const_mul _ _

theorem dini_old_scalar_change {psi : ℝ → ℝ} {eta B c R : ℝ}
    (he : 0 < eta) (he1 : eta < 1) (hB : 0 ≤ B) (hm : Measurable psi)
    (hpsi : ∀ s : ℝ, 0 < s → 0 ≤ psi s ∧ psi s ≤ B*s^eta) (hc : 0 < c) (hR : 0 < R) :
    (∫ a in Set.Ioi (R^2), a^(-(3/2:ℝ))*psi (c*Real.sqrt a))=
      2*c*(∫ s in Set.Ioi (c*R), psi s/s^2) :=
  (dini_old_scalar_data he he1 hB hm hpsi hc hR).2

end Yau.LeafProofs.L05Aux
