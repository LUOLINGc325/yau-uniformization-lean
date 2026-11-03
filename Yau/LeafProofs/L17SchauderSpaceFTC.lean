import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Convex.Basic

open Set Metric Filter MeasureTheory
open scoped Topology Interval
noncomputable section
set_option maxHeartbeats 1000000
namespace Yau.LeafProofs.L17SchauderAux

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- An actual segment FTC identity with a continuous proposed derivative
recovers the genuine Frechet derivative. -/
theorem hasFDerivAt_of_segment_integral {S : Set E} (hS : IsOpen S) (hConv : Convex ℝ S)
    {f : E → F} {J : E → E →L[ℝ] F} (hJ : ContinuousOn J S)
    (hFTC : ∀ x ∈ S, ∀ y ∈ S,
      f y-f x = ∫ theta in (0 : ℝ)..1, J (AffineMap.lineMap x y theta) (y-x))
    {x : E} (hx : x ∈ S) : HasFDerivAt f (J x) x := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  apply Asymptotics.IsLittleO.of_bound
  intro eps heps
  obtain ⟨delta,hdelta,hnear⟩ := Metric.continuousAt_iff.mp (hJ.continuousAt (hS.mem_nhds hx)) eps heps
  obtain ⟨r,hr,hrS⟩ := Metric.isOpen_iff.mp hS x hx
  filter_upwards [Metric.ball_mem_nhds (0 : E) (lt_min hdelta hr)] with h hh
  have hhNorm : ‖h‖ < min delta r := by simpa only [mem_ball,dist_zero_right] using hh
  have hy : x+h ∈ S := hrS (by simpa only [mem_ball,dist_eq_norm,add_sub_cancel_left] using hhNorm.trans_le (min_le_right _ _))
  have hpathCont : Continuous (fun theta : ℝ => AffineMap.lineMap x (x+h) theta) := by
    simp only [AffineMap.lineMap_apply_module']
    fun_prop
  have hpath : ContinuousOn (fun theta : ℝ => J (AffineMap.lineMap x (x+h) theta) h) (Icc (0 : ℝ) 1) :=
    (hJ.comp hpathCont.continuousOn (fun theta htheta => hConv.lineMap_mem hx hy htheta)).clm_apply continuousOn_const
  have hpathU : ContinuousOn (fun theta : ℝ => J (AffineMap.lineMap x (x+h) theta) h) (uIcc (0 : ℝ) 1) := by
    simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hpath
  have hInt : IntervalIntegrable (fun theta : ℝ => J (AffineMap.lineMap x (x+h) theta) h) volume 0 1 := hpathU.intervalIntegrable
  have hEq : f (x+h)-f x-J x h =
      ∫ theta in (0 : ℝ)..1, (J (AffineMap.lineMap x (x+h) theta)-J x) h := by
    rw [hFTC x hx (x+h) hy]
    simp only [add_sub_cancel_left]
    rw [show J x h = ∫ _theta in (0 : ℝ)..1, J x h by simp]
    rw [← intervalIntegral.integral_sub hInt intervalIntegrable_const]
    rfl
  rw [hEq]
  calc
    _ ≤ (eps*‖h‖)*|1-(0 : ℝ)| := intervalIntegral.norm_integral_le_of_norm_le_const (by
      intro theta htheta
      have ht : theta ∈ Icc (0 : ℝ) 1 := by
        exact Ioc_subset_Icc_self (by simpa only [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using htheta)
      have hdist : dist (AffineMap.lineMap x (x+h) theta) x < delta := by
        rw [AffineMap.lineMap_apply_module',dist_eq_norm]
        simp only [add_sub_cancel_right,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_nonneg ht.1]
        exact (mul_le_of_le_one_left (norm_nonneg h) ht.2).trans_lt (hhNorm.trans_le (min_le_left _ _))
      have hJn : ‖J (AffineMap.lineMap x (x+h) theta)-J x‖ ≤ eps := by
        simpa only [dist_eq_norm] using (hnear hdist).le
      exact ((J (AffineMap.lineMap x (x+h) theta)-J x).le_opNorm h).trans
        (mul_le_mul_of_nonneg_right hJn (norm_nonneg h)))
    _ = eps*‖h‖ := by norm_num

/-- Time FTC recovers the actual within derivative on the entire closed
interval, with both endpoints retained. -/
theorem hasDerivWithinAt_of_interval_integral {T : ℝ} (hT : 0 ≤ T)
    {f w : ℝ → F} (hw : Continuous w)
    (hFTC : ∀ s ∈ Icc (0 : ℝ) T, ∀ t ∈ Icc (0 : ℝ) T,
      f t-f s = ∫ tau in s..t, w tau) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    HasDerivWithinAt f (w t) (Icc (0 : ℝ) T) t := by
  have hInt := intervalIntegral.integral_hasDerivAt_right (hw.intervalIntegrable 0 t)
    hw.aestronglyMeasurable.stronglyMeasurableAtFilter hw.continuousAt
  have hPrim : HasDerivWithinAt (fun s => f 0+∫ tau in (0 : ℝ)..s, w tau) (w t) (Icc (0 : ℝ) T) t := by
    exact (hInt.const_add (f 0)).hasDerivWithinAt
  apply hPrim.congr
  · intro s hs
    have h := hFTC 0 ⟨le_rfl,hT⟩ s hs
    exact (eq_add_of_sub_eq h).trans (add_comm _ _)
  · have h := hFTC 0 ⟨le_rfl,hT⟩ t ht
    exact (eq_add_of_sub_eq h).trans (add_comm _ _)

end Yau.LeafProofs.L17SchauderAux
