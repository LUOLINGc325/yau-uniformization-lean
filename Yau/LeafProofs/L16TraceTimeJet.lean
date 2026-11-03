import Yau.LeafProofs.L16TraceTimeEquation
import Yau.LeafProofs.L16TraceTangentialHolder
import Yau.LeafProofs.L16ResidualEstimates

open MeasureTheory Filter Set
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates
local instance traceTimeJet_dualGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] ℝ) := inferInstance
local instance traceTimeJet_dualSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] ℝ) := inferInstance
local instance traceTimeJet_bilinearGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance
local instance traceTimeJet_bilinearSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance

/-- Taking the trace of the actual tangent Hessian commutes with its genuine
    integrable kernel, including the zero initial time. -/
theorem normalTraceTangentialSecond_trace_integral {n : ℕ} {α F H t a : ℝ}
    (hα : 0 < α) {B : Point n → ℝ} (hB : Continuous B) (hF : ∀ p, |B p| ≤ F)
    (hH0 : 0 ≤ H) (hH : ∀ s x y, |B (x,s)-B (y,s)| ≤ H*‖x-y‖^α)
    (ht : 0 ≤ t) (ha : 0 ≤ a) (ξ : Space n) :
    heatTrace (normalTraceTangentialSecond B t a ξ) =
      ∫ r in (0 : ℝ)..t, normalHeatProfile r a*heatLaplacian (heatAverage r (fun y => B (y,t-r))) ξ := by
  have hI := normalTraceTangentialSecond_integrable hα hB hF hH0 hH ht ha ξ
  calc
    _ = ∫ r in (0 : ℝ)..t, heatTrace (normalHeatProfile r a •
        fderiv ℝ (fderiv ℝ (heatAverage r (fun y => B (y,t-r)))) ξ) := by
      exact ((heatTrace (n := n)).intervalIntegral_comp_comm hI).symm
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro r hr
      simp only [map_smul,smul_eq_mul,heatTrace_apply,heatLaplacian]

/-- The actual causal time integral is the tangent trace minus the genuine
    parabolic Poisson normal jet. -/
theorem normalTraceAgeTimeDerivative_eq {n : ℕ} {α F H t a : ℝ}
    (hα : 0 < α) {B : Point n → ℝ} (hB : Continuous B) (hF : ∀ p, |B p| ≤ F)
    (hH0 : 0 ≤ H) (hH : ∀ s x y, |B (x,s)-B (y,s)| ≤ H*‖x-y‖^α)
    (ht : 0 ≤ t) (ha : 0 < a) (hPast : ∀ y s, s ≤ 0 → B (y,s) = 0) (ξ : Space n) :
    normalTraceAgeTimeDerivative B t a ξ =
      heatTrace (normalTraceTangentialSecond B t a ξ)-tracePoissonAverage a B (ξ,t) := by
  have hTTI := normalTraceTangentialSecond_integrable hα hB hF hH0 hH ht ha.le ξ
  have hTTTrace := normalTraceTangentialSecond_trace_integral hα hB hF hH0 hH ht ha.le ξ
  have hFun : (fun r => heatTrace (normalHeatProfile r a •
      fderiv ℝ (fderiv ℝ (heatAverage r (fun y => B (y,t-r)))) ξ)) =
      fun r => normalHeatProfile r a*heatLaplacian (heatAverage r (fun y => B (y,t-r))) ξ := by
    funext r
    simp only [map_smul,smul_eq_mul,heatTrace_apply,heatLaplacian]
  have hHI : IntervalIntegrable (fun r => normalHeatProfile r a*
      heatLaplacian (heatAverage r (fun y => B (y,t-r))) ξ) volume 0 t := by
    apply (intervalIntegrable_iff_integrableOn_Ioo_of_le ht).mpr
    have hi := (heatTrace (n := n)).integrable_comp
      ((intervalIntegrable_iff_integrableOn_Ioo_of_le ht).mp hTTI)
    rwa [show (fun r => heatTrace ((fun r => normalHeatProfile r a •
      fderiv ℝ (fderiv ℝ (heatAverage r (fun y => B (y,t-r)))) ξ) r)) =
      fun r => normalHeatProfile r a*heatLaplacian (heatAverage r (fun y => B (y,t-r))) ξ from hFun] at hi
  have hPI := (normalTraceFirst_hasDerivAt hB hF ht ha ξ).1
  have hSource : normalTraceAgeTimeDerivative B t a ξ = ∫ s in (0 : ℝ)..t,
      -normalPoissonKernel a (t-s)*heatAverage (t-s) (fun y => B (y,s)) ξ+
      normalHeatProfile (t-s) a*heatLaplacian (heatAverage (t-s) (fun y => B (y,s))) ξ := by
    rw [normalTraceAgeTimeDerivative,intervalIntegral.integral_of_le ht,
      intervalIntegral.integral_of_le ht,integral_Ioc_eq_integral_Ioo,integral_Ioc_eq_integral_Ioo]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    simp only [traceTimeKernel,ite_eq_left hs.2]
  have hReverse : (∫ s in (0 : ℝ)..t,
      -normalPoissonKernel a (t-s)*heatAverage (t-s) (fun y => B (y,s)) ξ+
      normalHeatProfile (t-s) a*heatLaplacian (heatAverage (t-s) (fun y => B (y,s))) ξ) =
      ∫ r in (0 : ℝ)..t, -normalPoissonKernel a r*heatAverage r (fun y => B (y,t-r)) ξ+
        normalHeatProfile r a*heatLaplacian (heatAverage r (fun y => B (y,t-r))) ξ := by
    simpa only [sub_self,sub_zero,sub_sub_cancel] using
      (intervalIntegral.integral_comp_sub_left
        (fun r => -normalPoissonKernel a r*heatAverage r (fun y => B (y,t-r)) ξ+
          normalHeatProfile r a*heatLaplacian (heatAverage r (fun y => B (y,t-r))) ξ)
        t (a := 0) (b := t))
  rw [hSource,hReverse]
  simp_rw [neg_mul]
  have hSum := intervalIntegral.integral_add hPI.neg hHI
  simp only [Pi.neg_apply] at hSum
  rw [intervalIntegral.integral_neg] at hSum
  change (∫ r in (0 : ℝ)..t, -(normalPoissonKernel a r*heatAverage r (fun y => B (y,t-r)) ξ)+
    normalHeatProfile r a*heatLaplacian (heatAverage r (fun y => B (y,t-r))) ξ) =
    -(∫ r in (0 : ℝ)..t, normalPoissonKernel a r*heatAverage r (fun y => B (y,t-r)) ξ)+
      ∫ r in (0 : ℝ)..t, normalHeatProfile r a*heatLaplacian (heatAverage r (fun y => B (y,t-r))) ξ at hSum
  rw [hSum,← hTTTrace,finite_tracePoisson_eq_average ha ht hPast ξ]
  ring

/-- The true tangent Hessian has a whole space-time Holder bound at every
    fixed nonnegative normal height. -/
theorem normalTraceTangentialSecond_fixed_normal_holder {n : ℕ} {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ {T a : ℝ}, 0 ≤ T → T ≤ 1 → 0 ≤ a →
      ∀ (B : Point n → ℝ) (F : ℝ), HolderBound α Set.univ B F →
      HolderBound α (cylinder Set.univ 0 T) (fun p => normalTraceTangentialSecond B p.2 a p.1) (C*F) := by
  obtain ⟨Cs,hCs,hSup⟩ := normalTraceTangentialSecond_bound (n := n) hα
  obtain ⟨Ch,hCh,hPair⟩ := normalTraceTangentialSecond_holder_bound (n := n) hα hα1
  refine ⟨Cs+Ch,by positivity,?_⟩
  intro T a hT hT1 ha B F hB
  have hF0 : 0 ≤ F := hB.1
  have hc : Continuous B := continuousOn_univ.mp (holderBound_continuousOn hα hB)
  have hb : ∀ p, |B p| ≤ F := fun p => hB.2.1 p (mem_univ _)
  have hh : ∀ s x y, |B (x,s)-B (y,s)| ≤ F*‖x-y‖^α := by
    intro s x y
    simpa only [holderWeight,sub_self,abs_zero,Real.zero_rpow (by positivity : α/2 ≠ 0),
      add_zero,Real.norm_eq_abs] using hB.2.2 (x,s) (mem_univ _) (y,s) (mem_univ _)
  refine ⟨by positivity,?_,?_⟩
  · intro p hp
    have hPow : p.2^(α/2) ≤ 1 := by
      simpa only [Real.one_rpow] using
        Real.rpow_le_rpow hp.2.1 (hp.2.2.trans hT1) (by positivity : 0 ≤ α/2)
    exact (hSup B F F hc hb hB.1 hh p.2 hp.2.1 a ha p.1).trans
      ((mul_le_of_le_one_right (by positivity) hPow).trans
        (mul_le_mul_of_nonneg_right (by linarith : Cs ≤ Cs+Ch) hB.1))
  · intro p hp q hq
    have h := hPair B F hB p.1 q.1 a a p.2 q.2 ha ha
      ⟨hp.2.1,hp.2.2.trans hT1⟩ ⟨hq.2.1,hq.2.2.trans hT1⟩
    simp only [sub_self,abs_zero,Real.zero_rpow hα.ne',add_zero] at h
    change _ ≤ (Cs+Ch)*F*holderWeight α p q
    apply h.trans
    apply mul_le_mul_of_nonneg_right
    · exact mul_le_mul_of_nonneg_right (by linarith : Ch ≤ Cs+Ch) hB.1
    · positivity

/-- The source plus the tangent trace minus the normal Poisson jet is the
    actual time-jet candidate. -/
def normalTraceTimeJet {n : ℕ} (B : Point n → ℝ) (a : ℝ) (p : Point n) : ℝ :=
  B p+heatTrace (normalTraceTangentialSecond B p.2 a p.1)-tracePoissonAverage a B p

/-- Actual Holder continuity of the time-jet candidate, uniformly in height. -/
theorem normalTraceTimeJet_fixed_normal_holder {n : ℕ} {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ {T a : ℝ}, 0 ≤ T → T ≤ 1 → 0 ≤ a →
      ∀ (B : Point n → ℝ) (F : ℝ), HolderBound α Set.univ B F →
      HolderBound α (cylinder Set.univ 0 T) (normalTraceTimeJet B a) (C*F) := by
  obtain ⟨C,hC,hTT⟩ := normalTraceTangentialSecond_fixed_normal_holder (n := n) hα hα1
  refine ⟨2+‖heatTrace (n := n)‖*C,by positivity,?_⟩
  intro T a hT hT1 ha B F hB
  have hF0 : 0 ≤ F := hB.1
  have hBQ : HolderBound α (cylinder Set.univ 0 T) B F := holderBound_mono hB (subset_univ _)
  have hPQ : HolderBound α (cylinder Set.univ 0 T) (tracePoissonAverage a B) F :=
    holderBound_mono (tracePoissonAverage_fixed_normal_holder hα ha hB) (subset_univ _)
  have h := holderBound_sub
    (holderBound_add hBQ (holderBound_comp_continuousLinearMap (heatTrace (n := n)) (hTT hT hT1 ha B F hB))) hPQ
  change HolderBound α (cylinder Set.univ 0 T)
    (fun p => B p+heatTrace (normalTraceTangentialSecond B p.2 a p.1)-tracePoissonAverage a B p)
    ((2+‖heatTrace (n := n)‖*C)*F)
  convert h using 1 <;> ring

/-- The true time derivative on every closed time interval, including its
    initial and terminal endpoints, follows from the actual primitive formula. -/
theorem normalTraceLayer_hasDerivWithinAt_time {n : ℕ} {α F T t a : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1)
    {B : Point n → ℝ} (hB : HolderBound α Set.univ B F)
    (hPast : ∀ y s, s ≤ 0 → B (y,s) = 0) (ha : 0 < a)
    (ht : t ∈ Icc 0 T) (ξ : Space n) :
    HasDerivWithinAt (fun r => normalTraceLayer B ξ r a)
      (normalTraceTimeJet B a (ξ,t)) (Icc 0 T) t := by
  have hc : Continuous B := continuousOn_univ.mp (holderBound_continuousOn hα hB)
  have hb : ∀ p, |B p| ≤ F := fun p => hB.2.1 p (mem_univ _)
  have hh : ∀ s x y, |B (x,s)-B (y,s)| ≤ F*‖x-y‖^α := by
    intro s x y
    simpa only [holderWeight,sub_self,abs_zero,Real.zero_rpow (by positivity : α/2 ≠ 0),
      add_zero,Real.norm_eq_abs] using hB.2.2 (x,s) (mem_univ _) (y,s) (mem_univ _)
  obtain ⟨C,hC,hJ⟩ := normalTraceTimeJet_fixed_normal_holder (n := n) hα hα1
  have hJc := holderBound_continuousOn hα (hJ hT.le hT1 ha.le B F hB)
  let A : ℝ → ℝ := fun r => normalTraceTimeJet B a (ξ,r)
  have hAc : ContinuousOn A (Icc 0 T) := hJc.comp
    ((continuous_const.prodMk continuous_id).continuousOn)
    (fun r hr => ⟨mem_univ _,hr⟩)
  have hEq (r : ℝ) (hr : r ∈ Icc 0 T) : normalTraceLayer B ξ r a = ∫ s in (0 : ℝ)..r, A s := by
    rcases hr.1.eq_or_lt with rfl | hr0
    · simp only [normalTraceLayer_initial,intervalIntegral.integral_same]
    have hE := normalTraceLayer_integrated_time_equation hα hc hb hB.1 hh hr0 ha ξ
    have hBI : IntervalIntegrable (fun s => B (ξ,s)) volume 0 r :=
      (hc.comp (continuous_const.prodMk continuous_id)).intervalIntegrable 0 r
    calc
      _ = (∫ s in (0 : ℝ)..r, B (ξ,s))+(∫ s in (0 : ℝ)..r, normalTraceAgeTimeDerivative B s a ξ) := hE.2
      _ = ∫ s in (0 : ℝ)..r, B (ξ,s)+normalTraceAgeTimeDerivative B s a ξ :=
        (intervalIntegral.integral_add hBI hE.1).symm
      _ = _ := by
        apply intervalIntegral.integral_congr
        intro s hs
        have hs0 : 0 ≤ s := (show s ∈ Icc 0 r by simpa only [uIcc_of_le hr0.le] using hs).1
        change B (ξ,s)+normalTraceAgeTimeDerivative B s a ξ = A s
        rw [normalTraceAgeTimeDerivative_eq hα hc hb hB.1 hh hs0 ha hPast ξ]
        dsimp only [A,normalTraceTimeJet]
        ring
  have hAi : IntervalIntegrable A volume 0 t :=
    (hAc.mono (Icc_subset_Icc le_rfl ht.2)).intervalIntegrable_of_Icc ht.1
  letI : Fact (t ∈ Icc 0 T) := ⟨ht⟩
  have hd := intervalIntegral.integral_hasDerivWithinAt_right hAi
    (s := Icc 0 T) (t := Icc 0 T)
    (hAc.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t) (hAc t ht)
  exact hd.congr_of_mem hEq ht

theorem normalTraceTimeJet_boundary {n : ℕ} (B : Point n → ℝ) (p : Point n) :
    normalTraceTimeJet B 0 p = 0 := by
  simp [normalTraceTimeJet,normalTraceTangentialSecond_boundary,tracePoissonAverage]

/-- The actual within-time derivative holds at every nonnegative height,
    including the full lateral face and both time endpoints. -/
theorem normalTraceLayer_hasDerivWithinAt_time_closed {n : ℕ} {α F T t a : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1)
    {B : Point n → ℝ} (hB : HolderBound α Set.univ B F)
    (hPast : ∀ y s, s ≤ 0 → B (y,s) = 0) (ha : 0 ≤ a)
    (ht : t ∈ Icc 0 T) (ξ : Space n) :
    HasDerivWithinAt (fun r => normalTraceLayer B ξ r a)
      (normalTraceTimeJet B a (ξ,t)) (Icc 0 T) t := by
  by_cases ha0 : a = 0
  · subst a
    have hFun : (fun r => normalTraceLayer B ξ r 0) = fun _ : ℝ => (0 : ℝ) :=
      funext (normalTraceLayer_boundary B ξ)
    rw [hFun,normalTraceTimeJet_boundary]
    exact hasDerivWithinAt_const t (Icc 0 T) 0
  · exact normalTraceLayer_hasDerivWithinAt_time hα hα1 hT hT1 hB hPast
      (lt_of_le_of_ne ha (Ne.symm ha0)) ht ξ

end Yau.LeafProofs.L16Aux
