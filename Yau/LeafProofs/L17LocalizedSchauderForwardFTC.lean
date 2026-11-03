import Yau.LeafProofs.L17SchauderSpaceFTC
import Mathlib.Analysis.Calculus.Deriv.AffineMap

open Set Metric MeasureTheory
open scoped Topology Interval
noncomputable section
namespace Yau.LeafProofs.L17LocalizedSchauderAux

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Actual derivatives and a continuous derivative field give the segment
identity used by the closed Schauder graph. -/
theorem segment_integral_of_hasFDerivAt {U : Set E} (hConv : Convex ℝ U)
    {f : E → F} {D : E → E →L[ℝ] F} (hD : ContinuousOn D U)
    (hf : ∀ x ∈ U, HasFDerivAt f (D x) x) {x y : E} (hx : x ∈ U) (hy : y ∈ U) :
    f y-f x = ∫ theta in (0 : ℝ)..1, D (AffineMap.lineMap x y theta) (y-x) := by
  have hPath : Continuous (fun theta : ℝ => AffineMap.lineMap x y theta) := by
    simp only [AffineMap.lineMap_apply_module']
    fun_prop
  have hInt : IntervalIntegrable (fun theta : ℝ => D (AffineMap.lineMap x y theta) (y-x)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact (hD.comp hPath.continuousOn (fun theta ht => hConv.lineMap_mem hx hy ht)).clm_apply continuousOn_const
  have hDeriv : ∀ theta ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun theta => f (AffineMap.lineMap x y theta))
        (D (AffineMap.lineMap x y theta) (y-x)) theta := by
    intro theta ht
    have ht' : theta ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
    exact (hf _ (hConv.lineMap_mem hx hy ht')).comp_hasDerivAt theta AffineMap.hasDerivAt_lineMap
  simpa only [AffineMap.lineMap_apply_zero,AffineMap.lineMap_apply_one] using
    (intervalIntegral.integral_eq_sub_of_hasDerivAt hDeriv hInt).symm

/-- Closed-interval within derivatives, including both endpoints, imply the
actual time FTC identity. -/
theorem interval_integral_of_hasDerivWithinAt {T : ℝ} {f D : ℝ → F}
    (hf : Continuous f) (hD : Continuous D)
    (hDeriv : ∀ x ∈ Icc (0 : ℝ) T, HasDerivWithinAt f (D x) (Icc (0 : ℝ) T) x)
    {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) T) (ht : t ∈ Icc (0 : ℝ) T) :
    f t-f s = ∫ tau in s..t, D tau := by
  apply Eq.symm
  apply intervalIntegral.integral_eq_sub_of_hasDeriv_right hf.continuousOn _ (hD.intervalIntegrable s t)
  intro x hx
  have hx0 : 0 < x := (le_min hs.1 ht.1).trans_lt hx.1
  have hxT : x < T := hx.2.trans_le (max_le hs.2 ht.2)
  exact ((hDeriv x ⟨hx0.le,hxT.le⟩).hasDerivAt (Icc_mem_nhds hx0 hxT)).hasDerivWithinAt

end Yau.LeafProofs.L17LocalizedSchauderAux
