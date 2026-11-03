import Yau.LeafProofs.L16HilbertTimeRegularization
import Yau.LeafProofs.L16WeakTimePrimitive

open MeasureTheory Filter Set
open scoped Topology ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16TimeReflection
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The zero extension uses the actual raw function on the open time slab. -/
def timeZeroExtension (T : ℝ) (U : ℝ → E) : ℝ → E := (Ioo 0 T).indicator U

/-- Three actual reflected copies, with harmless zero values at the joins. -/
def evenTimeReflection (T : ℝ) (U : ℝ → E) (t : ℝ) : E :=
  timeZeroExtension T U (-t) + timeZeroExtension T U t + timeZeroExtension T U (2*T-t)

def oddTimeReflection (T : ℝ) (U : ℝ → E) (t : ℝ) : E :=
  -timeZeroExtension T U (-t) + timeZeroExtension T U t - timeZeroExtension T U (2*T-t)

theorem timeZeroExtension_memLp {T : ℝ} {U : ℝ → E}
    (hU : MemLp U 2 (volume.restrict (Ioo 0 T))) :
    MemLp (timeZeroExtension T U) 2 volume :=
  (memLp_indicator_iff_restrict measurableSet_Ioo.nullMeasurableSet).mpr hU

theorem timeZeroExtension_compact (T : ℝ) (U : ℝ → E) :
    HasCompactSupport (timeZeroExtension T U) := by
  apply HasCompactSupport.of_support_subset_isCompact (K := Icc 0 T) isCompact_Icc
  intro t ht
  by_contra h
  apply ht
  exact Set.indicator_of_notMem (fun ht' => h (Ioo_subset_Icc_self ht')) U

theorem evenTimeReflection_memLp {T : ℝ} {U : ℝ → E}
    (hU : MemLp U 2 (volume.restrict (Ioo 0 T))) :
    MemLp (evenTimeReflection T U) 2 volume := by
  have hz := timeZeroExtension_memLp hU
  exact ((hz.comp_measurePreserving (Measure.measurePreserving_neg volume)).add hz).add
    (hz.comp_measurePreserving (volume.measurePreserving_sub_left (2*T)))

theorem oddTimeReflection_memLp {T : ℝ} {U : ℝ → E}
    (hU : MemLp U 2 (volume.restrict (Ioo 0 T))) :
    MemLp (oddTimeReflection T U) 2 volume := by
  have hz := timeZeroExtension_memLp hU
  exact ((hz.comp_measurePreserving (Measure.measurePreserving_neg volume)).neg.add hz).sub
    (hz.comp_measurePreserving (volume.measurePreserving_sub_left (2*T)))

theorem evenTimeReflection_compact (T : ℝ) (U : ℝ → E) :
    HasCompactSupport (evenTimeReflection T U) := by
  have hc := timeZeroExtension_compact T U
  exact ((hc.comp_homeomorph (Homeomorph.neg ℝ)).add hc).add
    (hc.comp_homeomorph (Homeomorph.subLeft (2*T)))

theorem oddTimeReflection_compact (T : ℝ) (U : ℝ → E) :
    HasCompactSupport (oddTimeReflection T U) := by
  have hc := timeZeroExtension_compact T U
  exact ((hc.comp_homeomorph (Homeomorph.neg ℝ)).neg.add hc).sub
    (hc.comp_homeomorph (Homeomorph.subLeft (2*T)))

theorem evenTimeReflection_eq_on_original {T : ℝ} {U : ℝ → E} {t : ℝ}
    (ht : t ∈ Ioo 0 T) : evenTimeReflection T U t = U t := by
  have hl : -t ∉ Ioo 0 T := by intro h; linarith [h.1,ht.1]
  have hr : 2*T-t ∉ Ioo 0 T := by intro h; linarith [h.2,ht.2]
  simp only [evenTimeReflection,timeZeroExtension,indicator_of_mem ht,
    indicator_of_notMem hl,indicator_of_notMem hr,zero_add,add_zero]

theorem oddTimeReflection_eq_on_original {T : ℝ} {U : ℝ → E} {t : ℝ}
    (ht : t ∈ Ioo 0 T) : oddTimeReflection T U t = U t := by
  have hl : -t ∉ Ioo 0 T := by intro h; linarith [h.1,ht.1]
  have hr : 2*T-t ∉ Ioo 0 T := by intro h; linarith [h.2,ht.2]
  simp only [oddTimeReflection,timeZeroExtension,indicator_of_mem ht,
    indicator_of_notMem hl,indicator_of_notMem hr,neg_zero,zero_add,sub_zero]

section Weighted
variable [CompleteSpace E]

theorem timeZeroExtension_weighted_integral (T : ℝ) (U : ℝ → E) (φ : ℝ → ℝ) :
    (∫ t, φ t • timeZeroExtension T U t) = ∫ t in Ioo 0 T, φ t • U t := by
  rw [← integral_indicator measurableSet_Ioo]
  congr 1
  funext t
  by_cases ht : t ∈ Ioo 0 T <;> simp [timeZeroExtension,ht]

theorem timeReflection_weighted_integral (T d : ℝ) (U : ℝ → E) (φ : ℝ → ℝ) :
    (∫ t, φ t • timeZeroExtension T U (d-t)) = ∫ t in Ioo 0 T, φ (d-t) • U t := by
  calc
    _ = ∫ t, φ (d-t) • timeZeroExtension T U t := by
      simpa only [sub_sub_cancel] using
        (integral_sub_left_eq_self
          (fun t => φ (d-t) • timeZeroExtension T U t) volume d)
    _ = _ := timeZeroExtension_weighted_integral T U _

theorem timeZeroExtension_weighted_integrable {T : ℝ} (hT : 0 ≤ T) {U : ℝ → E}
    (hU : IntegrableOn U (Ioo 0 T)) {φ : ℝ → ℝ} (hφ : Continuous φ) :
    Integrable (fun t => φ t • timeZeroExtension T U t) := by
  have hi : IntegrableOn (fun t => φ t • U t) (Ioo 0 T) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hT).mp
      (((intervalIntegrable_iff_integrableOn_Ioo_of_le hT).mpr hU).continuousOn_smul
        hφ.continuousOn)
  have hz := (integrable_indicator_iff measurableSet_Ioo).mpr hi
  convert hz using 1
  funext t
  by_cases ht : t ∈ Ioo 0 T <;> simp [timeZeroExtension,ht]

theorem timeReflection_weighted_integrable {T : ℝ} (hT : 0 ≤ T) {U : ℝ → E}
    (hU : IntegrableOn U (Ioo 0 T)) {φ : ℝ → ℝ} (hφ : Continuous φ) (d : ℝ) :
    Integrable (fun t => φ t • timeZeroExtension T U (d-t)) := by
  have hi := timeZeroExtension_weighted_integrable hT hU
    (hφ.comp (continuous_const.sub continuous_id) : Continuous (fun t : ℝ => φ (d-t)))
  simpa only [Function.comp_def,sub_sub_cancel] using hi.comp_sub_left d

theorem evenTimeReflection_weighted_integral {T : ℝ} (hT : 0 ≤ T) {U : ℝ → E}
    (hU : IntegrableOn U (Ioo 0 T)) {φ : ℝ → ℝ} (hφ : Continuous φ) :
    (∫ t, φ t • evenTimeReflection T U t) =
      ∫ t in Ioo 0 T, (φ (-t)+φ t+φ (2*T-t)) • U t := by
  have hl := timeReflection_weighted_integrable hT hU hφ 0
  simp only [zero_sub] at hl
  have hm := timeZeroExtension_weighted_integrable hT hU hφ
  have hr := timeReflection_weighted_integrable hT hU hφ (2*T)
  simp_rw [evenTimeReflection,smul_add]
  have hAdd := integral_add (hl.add hm) hr
  have hAdd2 := integral_add hl hm
  simp only [Pi.add_apply] at hAdd hAdd2
  rw [hAdd,hAdd2]
  rw [show (∫ t, φ t • timeZeroExtension T U (-t)) =
    ∫ t in Ioo 0 T, φ (-t) • U t by
      simpa only [zero_sub] using timeReflection_weighted_integral T 0 U φ,
    timeZeroExtension_weighted_integral,timeReflection_weighted_integral]
  have hil : IntegrableOn (fun t => φ (-t) • U t) (Ioo 0 T) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hT).mp
      (((intervalIntegrable_iff_integrableOn_Ioo_of_le hT).mpr hU).continuousOn_smul
        (hφ.comp continuous_neg).continuousOn)
  have him : IntegrableOn (fun t => φ t • U t) (Ioo 0 T) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hT).mp
      (((intervalIntegrable_iff_integrableOn_Ioo_of_le hT).mpr hU).continuousOn_smul hφ.continuousOn)
  have hir : IntegrableOn (fun t => φ (2*T-t) • U t) (Ioo 0 T) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hT).mp
      (((intervalIntegrable_iff_integrableOn_Ioo_of_le hT).mpr hU).continuousOn_smul
        (hφ.comp (continuous_const.sub continuous_id)).continuousOn)
  have hAddI := integral_add (hil.add him) hir
  have hAddI2 := integral_add hil him
  simp only [Pi.add_apply] at hAddI hAddI2
  rw [← hAddI2,← hAddI]
  congr 1
  funext t
  simp only [add_smul]

theorem time_weighted_integrableOn {T : ℝ} (hT : 0 ≤ T) {U : ℝ → E}
    (hU : IntegrableOn U (Ioo 0 T)) {φ : ℝ → ℝ} (hφ : Continuous φ) :
    IntegrableOn (fun t => φ t • U t) (Ioo 0 T) :=
  (intervalIntegrable_iff_integrableOn_Ioo_of_le hT).mp
    (((intervalIntegrable_iff_integrableOn_Ioo_of_le hT).mpr hU).continuousOn_smul hφ.continuousOn)

theorem oddTimeReflection_weighted_integral {T : ℝ} (hT : 0 ≤ T) {U : ℝ → E}
    (hU : IntegrableOn U (Ioo 0 T)) {φ : ℝ → ℝ} (hφ : Continuous φ) :
    (∫ t, φ t • oddTimeReflection T U t) =
      ∫ t in Ioo 0 T, (-φ (-t)+φ t-φ (2*T-t)) • U t := by
  have hl := timeReflection_weighted_integrable hT hU hφ 0
  simp only [zero_sub] at hl
  have hm := timeZeroExtension_weighted_integrable hT hU hφ
  have hr := timeReflection_weighted_integrable hT hU hφ (2*T)
  have hAdd := integral_add hl.neg hm
  have hSub := integral_sub (hl.neg.add hm) hr
  simp only [Pi.add_apply,Pi.sub_apply,Pi.neg_apply] at hAdd hSub
  simp_rw [oddTimeReflection,smul_sub,smul_add,smul_neg]
  rw [hSub,hAdd,integral_neg]
  rw [show (∫ t, φ t • timeZeroExtension T U (-t)) =
    ∫ t in Ioo 0 T, φ (-t) • U t by
      simpa only [zero_sub] using timeReflection_weighted_integral T 0 U φ,
    timeZeroExtension_weighted_integral,timeReflection_weighted_integral]
  have hil := time_weighted_integrableOn hT hU (hφ.comp continuous_neg)
  have him := time_weighted_integrableOn hT hU hφ
  have hir := time_weighted_integrableOn hT hU
    (hφ.comp (continuous_const.sub continuous_id) : Continuous (fun t : ℝ => φ (2*T-t)))
  have hAddI := integral_add hil.neg him
  have hSubI := integral_sub (hil.neg.add him) hir
  simp only [Pi.add_apply,Pi.sub_apply,Pi.neg_apply,Function.comp_def] at hAddI hSubI
  rw [← integral_neg,← hAddI,← hSubI]
  congr 1
  funext t
  simp only [sub_smul,add_smul,neg_smul]

/-- Reflection preserves the genuine weak derivative through both inner joins.
    Its endpoint cancellation follows from the actual Banach primitive IBP. -/
theorem reflected_weak_derivative {T : ℝ} (hT : 0 < T) {U R : ℝ → E}
    (hU : IntegrableOn U (Ioo 0 T)) (hR : IntegrableOn R (Ioo 0 T))
    (hw : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ioo 0 T →
      (∫ t in Ioo 0 T, deriv φ t • U t) = -(∫ t in Ioo 0 T, φ t • R t))
    {η : ℝ → ℝ} (hη : ContDiff ℝ ∞ η) (_hcη : HasCompactSupport η)
    (hSupp : tsupport η ⊆ Ioo (-T) (2*T)) :
    (∫ t, deriv η t • evenTimeReflection T U t) =
      -(∫ t, η t • oddTimeReflection T R t) := by
  obtain ⟨c,hc,-⟩ := Yau.L16WeakTimePrimitive.exists_weak_time_primitive hT hU hR hw
  let ψ : ℝ → ℝ := fun t => -η (-t)+η t-η (2*T-t)
  have hψ : ContDiff ℝ 1 ψ := by
    exact ((hη.comp contDiff_neg).neg.add hη).sub
      (hη.comp (contDiff_const.sub contDiff_id)) |>.of_le (by simp)
  have hdψ (t : ℝ) : deriv ψ t = deriv η (-t)+deriv η t+deriv η (2*T-t) := by
    have hd (s : ℝ) := ((hη.differentiable (by simp)).differentiableAt (x := s)).hasDerivAt
    have hneg := (hd (-t)).comp t (hasDerivAt_neg t)
    have hsub := (hd (2*T-t)).comp t ((hasDerivAt_const t (2*T)).sub (hasDerivAt_id t))
    have hh := ((hneg.neg.add (hd t)).sub hsub).deriv
    change deriv ψ t = -(deriv η (-t)*(-1))+deriv η t-deriv η (2*T-t)*(0-1) at hh
    simpa only [zero_sub,mul_neg_one,neg_neg,sub_neg_eq_add] using hh
  have hOuterR : η (2*T) = 0 := image_eq_zero_of_notMem_tsupport (by
    intro h
    exact (hSupp h).2.false)
  have hOuterL : η (-T) = 0 := image_eq_zero_of_notMem_tsupport (by
    intro h
    exact (hSupp h).1.false)
  have hψ0 : ψ 0 = 0 := by simp [ψ,hOuterR]
  have hψT : ψ T = 0 := by simp [ψ,show 2*T-T = T by ring,hOuterL]
  have hIBP := Yau.L16WeakTimePrimitive.weak_scalar_test_ibp hT hR c hc hψ
  rw [hψT,hψ0,zero_smul,zero_smul,sub_self,zero_sub] at hIBP
  rw [evenTimeReflection_weighted_integral hT.le hU (hη.continuous_deriv (by simp)),
    oddTimeReflection_weighted_integral hT.le hR hη.continuous]
  simpa only [hdψ,ψ] using hIBP

end Weighted

section Operator
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [CompleteSpace E]

theorem map_timeZeroExtension (L : V →L[ℝ] E) (T : ℝ) (U : ℝ → V) (t : ℝ) :
    L (timeZeroExtension T U t) = timeZeroExtension T (fun t => L (U t)) t := by
  by_cases ht : t ∈ Ioo 0 T <;> simp [timeZeroExtension,ht]

theorem map_evenTimeReflection (L : V →L[ℝ] E) (T : ℝ) (U : ℝ → V) (t : ℝ) :
    L (evenTimeReflection T U t) = evenTimeReflection T (fun t => L (U t)) t := by
  simp only [evenTimeReflection,map_add,map_timeZeroExtension]

/-- The actual reflected operator equation holds on the larger open slab,
    with no weak-derivative assertion at the two outside jumps. -/
theorem reflected_operator_weak_derivative (L : V →L[ℝ] E) {T : ℝ} (hT : 0 < T)
    {U : ℝ → V} {R : ℝ → E}
    (hU : MemLp U 2 (volume.restrict (Ioo 0 T)))
    (hR : MemLp R 2 (volume.restrict (Ioo 0 T)))
    (hw : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ioo 0 T →
      (∫ t in Ioo 0 T, deriv φ t • L (U t)) = -(∫ t in Ioo 0 T, φ t • R t)) :
    L16HilbertTimeRegularization.LocalWeakDerivative (Ioo (-T) (2*T)) L
      (evenTimeReflection T U) (oddTimeReflection T R) := by
  intro η hη hcη hsη
  simp_rw [map_evenTimeReflection]
  exact reflected_weak_derivative hT (L.integrable_comp (hU.integrable (by norm_num)))
    (hR.integrable (by norm_num)) hw hη hcη hsη

/-- Every convolution kernel of radius less than `T` stays inside the
    enlarged reflection interval at all target times, including the endpoints. -/
theorem translated_kernel_support_subset {T ε : ℝ} (hεT : ε < T)
    {ρ : ℝ → ℝ} (hρ : tsupport ρ ⊆ Icc (-ε) ε)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    {s | t-s ∈ tsupport ρ} ⊆ Ioo (-T) (2*T) := by
  intro s hs
  have h := hρ hs
  constructor <;> linarith [h.1,h.2,ht.1,ht.2]

end Operator

end Yau.LeafProofs.L16TimeReflection
