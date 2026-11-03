import Yau.LeafProofs.L05AutonomousTimeIncrementsSlopes
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open Set Filter MeasureTheory Metric
open scoped Topology Interval
noncomputable section
set_option maxHeartbeats 2000000
namespace Yau.LeafProofs.L05AutonomousAux

def autoContinuousExtension {a b : ℝ} (hab : a ≤ b) (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  f (projIcc a b hab t)

theorem auto_continuousExtension_continuous {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) : Continuous (autoContinuousExtension hab f) :=
  (continuousOn_iff_continuous_domRestrict.mp hf).comp continuous_projIcc

theorem auto_continuousExtension_eq {a b : ℝ} (hab : a ≤ b) (f : ℝ → ℝ) {t : ℝ} (ht : t∈Icc a b) :
    autoContinuousExtension hab f t=f t := by
  unfold autoContinuousExtension
  rw [projIcc_of_mem _ ht]

theorem auto_backward_average_tendsto {f : ℝ → ℝ} (hf : Continuous f) {h : ℝ} (hh : 0 < h) (t : ℝ) :
    Tendsto (fun k : ℕ => (∫ r in t-autoDyadicStep h k..t, f r)/autoDyadicStep h k)
      atTop (𝓝 (f t)) := by
  let P : ℝ → ℝ := fun x => ∫ r in (0 : ℝ)..x, f r
  have hP : HasDerivAt P (f t) t := intervalIntegral.integral_hasDerivAt_right
    (hf.intervalIntegrable 0 t) hf.aestronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt
  have hNeg : Tendsto (fun k : ℕ => -autoDyadicStep h k) atTop (𝓝[≠] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨by simpa only [neg_zero] using (auto_dyadicStep_tendsto h).neg,?_⟩
    exact Eventually.of_forall (fun k => by simp only [mem_compl_iff,mem_singleton_iff,neg_eq_zero]; exact (auto_dyadicStep_pos hh k).ne')
  have hConv := hP.tendsto_slope_zero.comp hNeg
  have hEq (k : ℕ) : (-autoDyadicStep h k)⁻¹ • (P (t+-autoDyadicStep h k)-P t)=
      (∫ r in t-autoDyadicStep h k..t, f r)/autoDyadicStep h k := by
    have hInt := intervalIntegral.integral_interval_sub_left (hf.intervalIntegrable (μ := volume) 0 t)
      (hf.intervalIntegrable (μ := volume) 0 (t-autoDyadicStep h k))
    rw [← hInt]
    dsimp only [P]
    simp only [smul_eq_mul,inv_neg,sub_eq_add_neg,div_eq_mul_inv]
    ring
  simpa only [Function.comp_def,hEq] using hConv

theorem auto_integral_backward_slope {f : ℝ → ℝ} (hf : Continuous f) (x y h : ℝ) :
    (∫ t in x..y, autoBackwardSlope f t h)=
      ((∫ t in y-h..y, f t)-(∫ t in x-h..x, f t))/h := by
  change (∫ t in x..y, (f t-f (t-h))/h)=_
  have hSub : IntervalIntegrable (fun t => f (t-h)) volume x y :=
    (hf.comp (continuous_id.sub continuous_const)).intervalIntegrable x y
  rw [intervalIntegral.integral_div,
    intervalIntegral.integral_sub (hf.intervalIntegrable (μ := volume) x y) hSub,
    intervalIntegral.integral_comp_sub_right,
    intervalIntegral.integral_interval_sub_interval_comm' (hf.intervalIntegrable x y)
      (hf.intervalIntegrable (x-h) (y-h)) (hf.intervalIntegrable x (x-h))]

theorem auto_uniform_backward_slopes_ftc {c d h : ℝ} (hh : 0 < h)
    {f V : ℝ → ℝ} (hf : Continuous f)
    (hUniform : TendstoUniformlyOn (fun k t => autoBackwardSlope f t (autoDyadicStep h k)) V atTop (Icc c d)) :
    ∀ x∈Icc c d, ∀ y∈Icc c d, f y-f x=∫ t in x..y, V t := by
  intro x hx y hy
  have hSub : uIcc x y ⊆ Icc c d := by
    intro t ht
    exact ⟨(le_min hx.1 hy.1).trans ht.1,ht.2.trans (max_le hx.2 hy.2)⟩
  have hCont (k : ℕ) : Continuous (fun t => autoBackwardSlope f t (autoDyadicStep h k)) :=
    (hf.sub (hf.comp (continuous_id.sub continuous_const))).div_const _
  have hI := TendstoUniformlyOn.tendsto_intervalIntegral_of_continuousOn (μ := volume)
    (Eventually.of_forall fun k => (hCont k).continuousOn) (hUniform.mono hSub)
  have hOther := (auto_backward_average_tendsto hf hh y).sub (auto_backward_average_tendsto hf hh x)
  have hTarget : Tendsto (fun k => ∫ t in x..y, autoBackwardSlope f t (autoDyadicStep h k))
      atTop (𝓝 (f y-f x)) := by
    convert hOther using 1
    ext k
    rw [auto_integral_backward_slope hf]
    ring
  exact (tendsto_nhds_unique hI hTarget).symm

theorem auto_hasDerivWithinAt_of_ftc {c d : ℝ} (hcd : c < d) {f V : ℝ → ℝ}
    (hV : ContinuousOn V (Icc c d))
    (hFTC : ∀ x∈Icc c d, ∀ y∈Icc c d, f y-f x=∫ t in x..y, V t)
    {t : ℝ} (ht : t∈Icc c d) : HasDerivWithinAt f (V t) (Icc c d) t := by
  let W := autoContinuousExtension hcd.le V
  have hW : Continuous W := auto_continuousExtension_continuous hcd.le hV
  have hEq (r : ℝ) (hr : r∈Icc c d) : W r=V r := auto_continuousExtension_eq hcd.le V hr
  have hFTC' (r : ℝ) (hr : r∈Icc c d) : f r-f c=∫ tau in c..r, W tau := by
    rw [hFTC c ⟨le_rfl,hcd.le⟩ r hr]
    apply intervalIntegral.integral_congr
    intro tau htau
    exact (hEq tau ⟨(le_min le_rfl hr.1).trans htau.1,htau.2.trans (max_le hcd.le hr.2)⟩).symm
  have hInt := intervalIntegral.integral_hasDerivAt_right (hW.intervalIntegrable c t)
    hW.aestronglyMeasurable.stronglyMeasurableAtFilter hW.continuousAt
  have hPrim : HasDerivWithinAt (fun r => f c+∫ tau in c..r, W tau) (V t) (Icc c d) t := by
    rw [← hEq t ht]
    exact (hInt.const_add (f c)).hasDerivWithinAt
  apply hPrim.congr
  · intro r hr
    linarith [hFTC' r hr]
  · linarith [hFTC' t ht]

theorem auto_hasDerivAt_of_ftc {c d : ℝ} (hcd : c < d) {f V : ℝ → ℝ}
    (hV : ContinuousOn V (Icc c d))
    (hFTC : ∀ x∈Icc c d, ∀ y∈Icc c d, f y-f x=∫ t in x..y, V t)
    {t : ℝ} (ht : t∈Ioo c d) : HasDerivAt f (V t) t :=
  (auto_hasDerivWithinAt_of_ftc hcd hV hFTC ⟨ht.1.le,ht.2.le⟩).hasDerivAt
    (Icc_mem_nhds ht.1 ht.2)

end Yau.LeafProofs.L05AutonomousAux
