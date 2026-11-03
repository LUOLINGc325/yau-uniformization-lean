import Yau.LeafProofs.L19

/-! Joint regularity of the actual heat and logarithmic differential
quantities, obtained by differentiating their displayed chart formulas. -/

noncomputable section

open MeasureTheory Filter
open scoped Topology ContDiff Manifold Matrix ComplexOrder

namespace Yau.LeafProofs.L19Aux

open L18Aux

variable {n : ℕ} {M : ComplexManifold n}

/-- Ordinary time differentiation preserves joint smoothness on the
original open positive-time domain. -/
theorem smoothSpaceTime_time_derivative {u : M.Carrier → ℝ → ℝ}
    (hu : SmoothSpaceTime u (Set.Ioi 0)) :
    SmoothSpaceTime (fun x t => deriv (u x) t) (Set.Ioi 0) := by
  intro a
  let F : ComplexVector n × ℝ → ℝ := fun p => u (chartInv a p.1) p.2
  let U : Set (ComplexVector n × ℝ) := chartTarget a ×ˢ Set.Ioi 0
  have hU : IsOpen U := (isOpen_extChartAt_target (I := ComplexModel n) a).prod isOpen_Ioi
  have hF : ContDiffOn ℝ ∞ F U := hu a
  have hD : ContDiffOn ℝ ∞ (fderiv ℝ F) U :=
    hF.fderiv_of_isOpen hU (by simp)
  have hfield : ContDiffOn ℝ ∞ (fun p => fderiv ℝ F p (0, 1)) U :=
    hD.clm_apply contDiffOn_const
  apply hfield.congr
  intro p hp
  have hd := (hF.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  have hmap : HasDerivAt (fun s : ℝ => (p.1, s)) (0, 1) p.2 :=
    (hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2)
  simpa only [Function.comp_def, F] using
    (hd.hasFDerivAt.comp_hasDerivAt p.2 hmap).deriv

/-- A spatial directional derivative is a directional derivative of the
joint chart function, with zero time component. -/
theorem smoothSpaceTime_spatial_direction {u : M.Carrier → ℝ → ℝ}
    (hu : SmoothSpaceTime u (Set.Ioi 0)) (a : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget a) {t : ℝ} (ht : 0 < t)
    (i : RIdx n) :
    rDeriv (fun w => u (chartInv a w) t) z i =
      fderiv ℝ (fun p : ComplexVector n × ℝ => u (chartInv a p.1) p.2)
        (z, t) (realVec i, 0) := by
  let F : ComplexVector n × ℝ → ℝ := fun p => u (chartInv a p.1) p.2
  have hU : IsOpen (chartTarget a ×ˢ Set.Ioi (0 : ℝ)) :=
    (isOpen_extChartAt_target (I := ComplexModel n) a).prod isOpen_Ioi
  have hmem : (z, t) ∈ chartTarget a ×ˢ Set.Ioi (0 : ℝ) := ⟨hz, ht⟩
  have hd : DifferentiableAt ℝ F (z, t) :=
    ((hu a).contDiffAt (hU.mem_nhds hmem)).differentiableAt (by simp)
  have hmap : HasFDerivAt (fun w : ComplexVector n => (w, t))
      ((ContinuousLinearMap.id ℝ (ComplexVector n)).prod 0) z :=
    (hasFDerivAt_id z).prodMk (hasFDerivAt_const t z)
  have hc := (hd.hasFDerivAt.comp z hmap).fderiv
  have he := congrArg (fun L : ComplexVector n →L[ℝ] ℝ => L (realVec i)) hc
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply,
    zero_apply, rDeriv, F] using he

/-- The unrestricted time derivative is the joint differential in the
actual unit time direction. -/
theorem smoothSpaceTime_time_direction {u : M.Carrier → ℝ → ℝ}
    (hu : SmoothSpaceTime u (Set.Ioi 0)) (a : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget a) {t : ℝ} (ht : 0 < t) :
    deriv (u (chartInv a z)) t =
      fderiv ℝ (fun p : ComplexVector n × ℝ => u (chartInv a p.1) p.2)
        (z, t) (0, 1) := by
  have hU : IsOpen (chartTarget a ×ˢ Set.Ioi (0 : ℝ)) :=
    (isOpen_extChartAt_target (I := ComplexModel n) a).prod isOpen_Ioi
  have hmem : (z, t) ∈ chartTarget a ×ˢ Set.Ioi (0 : ℝ) := ⟨hz, ht⟩
  have hd := ((hu a).contDiffAt (hU.mem_nhds hmem)).differentiableAt (by simp)
  have hmap : HasDerivAt (fun s : ℝ => (z, s)) (0, 1) t :=
    (hasDerivAt_const t z).prodMk (hasDerivAt_id t)
  simpa only [Function.comp_def] using (hd.hasFDerivAt.comp_hasDerivAt t hmap).deriv

/-- Mixed ordinary spatial and time differentiation commute because the
joint chart Hessian is symmetric. -/
theorem smoothSpaceTime_spatial_time_hasDerivAt {u : M.Carrier → ℝ → ℝ}
    (hu : SmoothSpaceTime u (Set.Ioi 0)) (a : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget a) {t : ℝ} (ht : 0 < t)
    (i : RIdx n) :
    HasDerivAt (fun s => rDeriv (fun w => u (chartInv a w) s) z i)
      (rDeriv (fun w => deriv (u (chartInv a w)) t) z i) t := by
  let F : ComplexVector n × ℝ → ℝ := fun p => u (chartInv a p.1) p.2
  have hU : IsOpen (chartTarget a ×ˢ Set.Ioi (0 : ℝ)) :=
    (isOpen_extChartAt_target (I := ComplexModel n) a).prod isOpen_Ioi
  have hmem : (z, t) ∈ chartTarget a ×ˢ Set.Ioi (0 : ℝ) := ⟨hz, ht⟩
  have hF : ContDiffAt ℝ 2 F (z, t) :=
    ((hu a).contDiffAt (hU.mem_nhds hmem)).of_le (by simp)
  have hDF : DifferentiableAt ℝ (fderiv ℝ F) (z, t) :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hmapT : HasDerivAt (fun s : ℝ => (z, s)) (0, 1) t :=
    (hasDerivAt_const t z).prodMk (hasDerivAt_id t)
  have hT : HasDerivAt (fun s => fderiv ℝ F (z, s) (realVec i, 0))
      (fderiv ℝ (fderiv ℝ F) (z, t) (0, 1) (realVec i, 0)) t := by
    simpa only [Function.comp_def, map_zero, add_zero] using
      (hDF.hasFDerivAt.comp_hasDerivAt t hmapT).clm_apply
        (hasDerivAt_const t (realVec i, 0))
  have hS : HasFDerivAt (fun w => fderiv ℝ F (w, t) (0, 1))
      (((fderiv ℝ (fderiv ℝ F) (z, t)).comp
        ((ContinuousLinearMap.id ℝ (ComplexVector n)).prod 0)).flip (0, 1)) z := by
    have hmapS : HasFDerivAt (fun w : ComplexVector n => (w, t))
        ((ContinuousLinearMap.id ℝ (ComplexVector n)).prod 0) z :=
      (hasFDerivAt_id z).prodMk (hasFDerivAt_const t z)
    simpa only [Function.comp_def, ContinuousLinearMap.comp_zero, zero_add] using
      (hDF.hasFDerivAt.comp z hmapS).clm_apply (hasFDerivAt_const (0, 1) z)
  have htimeEq : (fun w => deriv (u (chartInv a w)) t) =ᶠ[𝓝 z]
      (fun w => fderiv ℝ F (w, t) (0, 1)) := by
    filter_upwards [(isOpen_extChartAt_target (I := ComplexModel n) a).mem_nhds hz]
      with w hw
    exact smoothSpaceTime_time_direction hu a hw ht
  have hSpaceValue : rDeriv (fun w => deriv (u (chartInv a w)) t) z i =
      fderiv ℝ (fderiv ℝ F) (z, t) (realVec i, 0) (0, 1) := by
    unfold rDeriv
    rw [htimeEq.fderiv_eq, hS.fderiv]
    rfl
  rw [hSpaceValue, hF.isSymmSndFDerivAt (by norm_num) (realVec i, 0) (0, 1)]
  apply hT.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ht] with s hs
  exact smoothSpaceTime_spatial_direction hu a hz hs i

set_option backward.isDefEq.respectTransparency false in
/-- The actual physical gradient pairing is jointly smooth for jointly
smooth scalars and the original smooth metric. -/
theorem smoothSpaceTime_scalarGradientPair (g : SmoothMetric M)
    {u v : M.Carrier → ℝ → ℝ}
    (hu : SmoothSpaceTime u (Set.Ioi 0)) (hv : SmoothSpaceTime v (Set.Ioi 0)) :
    SmoothSpaceTime (fun x t =>
      scalarGradientPair g.form (fun y => u y t) (fun y => v y t) x) (Set.Ioi 0) := by
  intro a
  let U : Set (ComplexVector n × ℝ) := chartTarget a ×ˢ Set.Ioi 0
  have hU : IsOpen U := (isOpen_extChartAt_target (I := ComplexModel n) a).prod isOpen_Ioi
  let F : ComplexVector n × ℝ → ℝ := fun p => u (chartInv a p.1) p.2
  let G : ComplexVector n × ℝ → ℝ := fun p => v (chartInv a p.1) p.2
  have hDF : ContDiffOn ℝ ∞ (fderiv ℝ F) U :=
    (hu a).fderiv_of_isOpen hU (by simp)
  have hDG : ContDiffOn ℝ ∞ (fderiv ℝ G) U :=
    (hv a).fderiv_of_isOpen hU (by simp)
  have hfield : ContDiffOn ℝ ∞ (fun p : ComplexVector n × ℝ =>
      ∑ i, ∑ j, (realMetricFn g.form a p.1)⁻¹ i j *
        fderiv ℝ F p (realVec i, 0) * fderiv ℝ G p (realVec j, 0)) U := by
    apply ContDiffOn.sum
    intro i hi
    apply ContDiffOn.sum
    intro j hj
    exact (((realMetricFn_inverse_contDiffOn g a i j).comp contDiffOn_fst
      (fun p hp => hp.1)).mul (hDF.clm_apply contDiffOn_const)).mul
        (hDG.clm_apply contDiffOn_const)
  apply hfield.congr
  intro p hp
  dsimp only
  rw [scalarGradientPair_eq_chart g.form (smoothSpaceTime_slice hu hp.2)
    (smoothSpaceTime_slice hv hp.2) a hp.1, chartGradientPair_eq_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  exact congrArg₂ (fun A B : ℝ => (realMetricFn g.form a p.1)⁻¹ i j * A * B)
    (smoothSpaceTime_spatial_direction hu a hp.1 hp.2 i)
    (smoothSpaceTime_spatial_direction hv a hp.1 hp.2 j)

theorem smoothSpaceTime_gradNormSq (g : SmoothMetric M)
    {u : M.Carrier → ℝ → ℝ} (hu : SmoothSpaceTime u (Set.Ioi 0)) :
    SmoothSpaceTime (fun x t => gradNormSq g.form (fun y => u y t) x) (Set.Ioi 0) := by
  have hpair := smoothSpaceTime_scalarGradientPair g hu hu
  intro a
  have hfield := (hpair a).div_const 2
  apply hfield.congr
  intro p hp
  dsimp only
  rw [scalarGradientPair_eq_twice_gradNormSq g.form (smoothSpaceTime_slice hu hp.2)]
  ring

theorem positiveHeatSolution_laplacian_smoothSpaceTime (h : HermitianField M)
    {u : M.Carrier → ℝ → ℝ} (hu : LeafCandidates.PositiveHeatSolution h u) :
    SmoothSpaceTime (fun x t => laplacian h (fun y => u y t) x) (Set.Ioi 0) := by
  have htime := smoothSpaceTime_time_derivative hu.1
  intro a
  exact (htime a).congr (fun p hp => (hu.2 (chartInv a p.1) p.2 hp.2).2.symm)

theorem positiveHeatSolution_log_laplacian_smoothSpaceTime (g : SmoothMetric M)
    {u : M.Carrier → ℝ → ℝ} (hu : LeafCandidates.PositiveHeatSolution g.form u) :
    SmoothSpaceTime (fun x t =>
      laplacian g.form (fun y => Real.log (u y t)) x) (Set.Ioi 0) := by
  have hlog := positiveHeatSolution_log_smoothSpaceTime g.form hu
  have htime := smoothSpaceTime_time_derivative hlog
  have hgrad := smoothSpaceTime_gradNormSq g hlog
  intro a
  apply ((htime a).sub (hgrad a)).congr
  intro p hp
  dsimp only
  rw [positiveHeatSolution_log_equation g.form hu (chartInv a p.1) hp.2]
  ring

end Yau.LeafProofs.L19Aux
