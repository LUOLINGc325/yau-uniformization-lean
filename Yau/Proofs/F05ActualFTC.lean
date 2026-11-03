import Mathlib

/-! Actual derivatives imply the spatial segment and closed-time FTC
constraints used to encode genuine functions in the Banach jet graph. -/

open Set MeasureTheory
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 1800000
namespace Yau.Proofs.F05Aux

theorem F05_actual_segment_ftc {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {D : Set E} (hD : Convex ℝ D) {f : E → F} {G : E → E →L[ℝ] F}
    (hG : ContinuousOn G D) (hf : ∀ x ∈ D, HasFDerivAt f (G x) x)
    {z w : E} (hz : z ∈ D) (hw : w ∈ D) :
    f w-f z = (∫ r in (0 : ℝ)..1,G (AffineMap.lineMap z w r)) (w-z) := by
  have hMap : MapsTo (AffineMap.lineMap z w) (Icc (0 : ℝ) 1) D :=
    fun r hr => hD.lineMap_mem hz hw hr
  have hLine : Continuous (fun r : ℝ => AffineMap.lineMap z w r) := by fun_prop
  have hContinuous : ContinuousOn (fun r => G (AffineMap.lineMap z w r)) (Icc (0 : ℝ) 1) :=
    hG.comp hLine.continuousOn hMap
  have hIntegrable : IntervalIntegrable (fun r => G (AffineMap.lineMap z w r)) volume 0 1 :=
    hContinuous.intervalIntegrable_of_Icc (by norm_num : (0 : ℝ) ≤ 1)
  have hApplyContinuous : ContinuousOn
      (fun r => G (AffineMap.lineMap z w r) (w-z)) (Icc (0 : ℝ) 1) :=
    hContinuous.clm_apply continuousOn_const
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun r : ℝ => f (AffineMap.lineMap z w r))
    (f' := fun r : ℝ => G (AffineMap.lineMap z w r) (w-z)) (by
      intro r hr
      have hr' : r ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hr
      exact (hf _ (hMap hr')).comp_hasDerivAt r (AffineMap.hasDerivAt_lineMap))
    (hApplyContinuous.intervalIntegrable_of_Icc (by norm_num : (0 : ℝ) ≤ 1))
  have hComm := (ContinuousLinearMap.apply ℝ F (w-z)).intervalIntegral_comp_comm hIntegrable
  change (∫ r in (0 : ℝ)..1,G (AffineMap.lineMap z w r) (w-z)) =
    (∫ r in (0 : ℝ)..1,G (AffineMap.lineMap z w r)) (w-z) at hComm
  calc
    f w-f z = ∫ r in (0 : ℝ)..1,G (AffineMap.lineMap z w r) (w-z) := by
      simpa only [AffineMap.lineMap_apply_zero,AffineMap.lineMap_apply_one] using hFTC.symm
    _ = _ := hComm

theorem F05_actual_time_ftc {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] {T s t : ℝ} {f K : ℝ → F}
    (hK : ContinuousOn K (Icc 0 T))
    (hD : ∀ r ∈ Icc 0 T, HasDerivWithinAt f (K r) (Icc 0 T) r)
    (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) :
    f t-f s = ∫ r in s..t,K r := by
  have hSub : uIcc s t ⊆ Icc 0 T := uIcc_subset_Icc hs ht
  have hf : ContinuousOn f (Icc 0 T) := fun r hr => (hD r hr).continuousWithinAt
  apply Eq.symm
  apply intervalIntegral.integral_eq_sub_of_hasDeriv_right (hf.mono hSub) _
    ((hK.mono hSub).intervalIntegrable)
  intro r hr
  have hmin : 0 ≤ min s t := le_min hs.1 ht.1
  have hmax : max s t ≤ T := max_le hs.2 ht.2
  have hr0 : 0 < r := hmin.trans_lt hr.1
  have hrT : r < T := hr.2.trans_le hmax
  exact ((hD r ⟨hr0.le,hrT.le⟩).hasDerivAt (Icc_mem_nhds hr0 hrT)).hasDerivWithinAt

end Yau.Proofs.F05Aux
