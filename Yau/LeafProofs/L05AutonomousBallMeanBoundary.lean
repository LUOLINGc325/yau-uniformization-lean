import Yau.LeafProofs.L05AutonomousBallMeanKernelSmooth

open Set Filter MeasureTheory Metric
open scoped Topology Interval
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05AutonomousAux

theorem auto_green_outer_bounds (d : ℕ) (omega : ℝ) {r : ℝ} (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ s∈Icc (r/2) r,
      |-autoGreenIntegrand d r s/((d : ℝ)*omega)| ≤ C*(r-s) ∧
      |autoGreenPrimitive d omega r s| ≤ C*(r-s)^2 := by
  let G : ℝ → ℝ := fun s => -autoGreenIntegrand d r s/((d : ℝ)*omega)
  let D : ℝ → ℝ := fun s => -((1-(d : ℝ))*s^(-(d : ℝ))-1/r^d)/((d : ℝ)*omega)
  have hGDeriv (s : ℝ) (hs : 0 < s) : HasDerivAt G (D s) s := by
    convert! (auto_greenIntegrand_hasDerivAt d (r := r) hs).neg.div_const ((d : ℝ)*omega) using 1
  have hGCont : ContinuousOn G (Ioi 0) :=
    (auto_greenIntegrand_continuousOn d r).neg.div_const ((d : ℝ)*omega)
  have hDCont : ContinuousOn D (Icc (r/2) r) := by
    intro s hs
    have hPos : 0 < s := (half_pos hr).trans_le hs.1
    have hPow : ContinuousAt (fun t : ℝ => t^(-(d : ℝ))) s :=
      continuousAt_id.rpow_const (Or.inl hPos.ne')
    have hAt : ContinuousAt D s :=
      ((hPow.const_mul (1-(d : ℝ))).sub continuousAt_const).neg.div_const ((d : ℝ)*omega)
    exact hAt.continuousWithinAt
  obtain ⟨M,hM⟩ := (isCompact_Icc.image_of_continuousOn hDCont.norm).bddAbove
  let C := max 1 M
  have hC : 0 < C := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hBound (s : ℝ) (hs : s∈Icc (r/2) r) : ‖D s‖ ≤ C :=
    (hM ⟨s,hs,rfl⟩).trans (le_max_right _ _)
  have hGR : G r=0 := by
    dsimp only [G]
    rw [autoGreenIntegrand,Real.rpow_sub hr,Real.rpow_one,Real.rpow_natCast,sub_self,neg_zero,zero_div]
  have hGAll : ∀ s∈Icc (r/2) r, |G s| ≤ C*(r-s) := by
    intro s hs
    have hSub : uIcc s r ⊆ Icc (r/2) r := by
      rw [uIcc_of_le hs.2]
      intro t ht
      exact ⟨hs.1.trans ht.1,ht.2⟩
    have hIntD : IntervalIntegrable D volume s r := (hDCont.mono hSub).intervalIntegrable
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => hGDeriv t ((half_pos hr).trans_le (hSub ht).1)) hIntD
    have hNorm : ‖∫ t in s..r, D t‖ ≤ C*|r-s| :=
      intervalIntegral.norm_integral_le_of_norm_le_const
        (fun t ht => hBound t (hSub (uIoc_subset_uIcc ht)))
    rw [hFTC,hGR,zero_sub,norm_neg,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hs.2)] at hNorm
    exact hNorm
  refine ⟨C,hC,?_⟩
  intro s hs
  refine ⟨hGAll s hs,?_⟩
  have hSub : uIcc s r ⊆ Icc (r/2) r := by
    rw [uIcc_of_le hs.2]
    intro t ht
    exact ⟨hs.1.trans ht.1,ht.2⟩
  have hGInt : IntervalIntegrable G volume s r :=
    (hGCont.mono (fun t ht => (half_pos hr).trans_le (hSub ht).1)).intervalIntegrable
  have hAbsInt : IntervalIntegrable (fun t => |G t|) volume s r := by simpa only [Real.norm_eq_abs] using hGInt.norm
  have hLinearInt : IntervalIntegrable (fun t : ℝ => C*(r-t)) volume s r :=
    (continuous_const.mul (continuous_const.sub continuous_id)).intervalIntegrable s r
  have hMono := intervalIntegral.integral_mono_on hs.2 hAbsInt hLinearInt
    (fun t ht => hGAll t ⟨hs.1.trans ht.1,ht.2⟩)
  have hId : IntervalIntegrable (fun t : ℝ => t) volume s r := continuous_id.intervalIntegrable s r
  have hConst : IntervalIntegrable (fun _t : ℝ => r) volume s r := intervalIntegrable_const
  have hPoly : (∫ t in s..r, C*(r-t))=C*(r-s)^2/2 := by
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_sub hConst hId,
      intervalIntegral.integral_const,integral_id]
    simp only [smul_eq_mul]
    ring
  rw [hPoly] at hMono
  have hK : autoGreenPrimitive d omega r s=-(∫ t in s..r, G t) := by
    dsimp only [autoGreenPrimitive,G]
    rw [intervalIntegral.integral_div,intervalIntegral.integral_neg]
    ring
  rw [hK,abs_neg]
  have hNorm : |∫ t in s..r, G t| ≤ ∫ t in s..r, |G t| := by
    simpa only [Real.norm_eq_abs] using intervalIntegral.norm_integral_le_integral_norm (μ := volume) (f := G) hs.2
  have hBoundK := hNorm.trans hMono
  exact hBoundK.trans (by nlinarith [mul_nonneg hC.le (sq_nonneg (r-s))])


theorem auto_radialGreen_hasDerivAt_outer (d : ℕ) (omega : ℝ) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (autoRadialGreen d omega r) 0 r := by
  have hAt : autoRadialGreen d omega r r=0 := by simp [autoRadialGreen]
  have hLeft : HasDerivWithinAt (autoRadialGreen d omega r) 0 (Icc (r/2) r) r := by
    apply (auto_green_primitive_hasDerivAt_outer d omega hr).hasDerivWithinAt.congr
    · intro s hs
      rcases eq_or_lt_of_le hs.2 with h|h
      · subst s
        simpa only [auto_green_primitive_outer] using hAt
      · change (if 0 < s ∧ s < r then autoGreenPrimitive d omega r s else 0)=_
        exact ite_eq_left ⟨(half_pos hr).trans_le hs.1,h⟩
    · simpa only [auto_green_primitive_outer] using hAt
  have hRight : HasDerivWithinAt (autoRadialGreen d omega r) 0 (Icc r (2*r)) r := by
    apply (hasDerivAt_const r (0 : ℝ)).hasDerivWithinAt.congr
    · intro s hs
      exact auto_radialGreen_zero_outside d omega r (fun h => not_lt_of_ge hs.1 h.2)
    · exact hAt
  apply (hLeft.union hRight).hasDerivAt
  apply mem_of_superset (Ioo_mem_nhds (by linarith : r/2 < r) (by linarith : r < 2*r))
  intro s hs
  rcases le_total s r with h|h
  · exact Or.inl ⟨hs.1.le,h⟩
  · exact Or.inr ⟨h,hs.2.le⟩

end Yau.LeafProofs.L05AutonomousAux
