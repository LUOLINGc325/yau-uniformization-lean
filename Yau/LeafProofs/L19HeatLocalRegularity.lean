import Yau.LeafProofs.L19HeatCaccioppoli

/-! Joint calculus on arbitrary open time domains, for finite-slab heat duality. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold Matrix ComplexOrder
namespace Yau.LeafProofs.L19Aux.LocalTime
open L18Aux
variable {n : ℕ} {M : ComplexManifold n} {I : Set ℝ}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
theorem smoothSpaceTime_time_derivative (hI : IsOpen I) {u : M.Carrier → ℝ → ℝ}
    (hu : SmoothSpaceTime u (I)) :
    SmoothSpaceTime (fun x t => deriv (u x) t) (I) := by
  intro a
  let F : ComplexVector n × ℝ → ℝ := fun p => u (chartInv a p.1) p.2
  let U : Set (ComplexVector n × ℝ) := chartTarget a ×ˢ I
  have hU : IsOpen U := (isOpen_extChartAt_target (I := ComplexModel n) a).prod hI
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
theorem smoothSpaceTime_spatial_direction (hI : IsOpen I) {u : M.Carrier → ℝ → ℝ}
    (hu : SmoothSpaceTime u (I)) (a : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget a) {t : ℝ} (ht : t ∈ I)
    (i : RIdx n) :
    rDeriv (fun w => u (chartInv a w) t) z i =
      fderiv ℝ (fun p : ComplexVector n × ℝ => u (chartInv a p.1) p.2)
        (z, t) (realVec i, 0) := by
  let F : ComplexVector n × ℝ → ℝ := fun p => u (chartInv a p.1) p.2
  have hU : IsOpen (chartTarget a ×ˢ I) :=
    (isOpen_extChartAt_target (I := ComplexModel n) a).prod hI
  have hmem : (z, t) ∈ chartTarget a ×ˢ I := ⟨hz, ht⟩
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


theorem smoothSpaceTime_scalarGradientPair (hI : IsOpen I) (g : SmoothMetric M)
    {u v : M.Carrier → ℝ → ℝ}
    (hu : SmoothSpaceTime u (I)) (hv : SmoothSpaceTime v (I)) :
    SmoothSpaceTime (fun x t =>
      scalarGradientPair g.form (fun y => u y t) (fun y => v y t) x) (I) := by
  intro a
  let U : Set (ComplexVector n × ℝ) := chartTarget a ×ˢ I
  have hU : IsOpen U := (isOpen_extChartAt_target (I := ComplexModel n) a).prod hI
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
    (smoothSpaceTime_spatial_direction hI hu a hp.1 hp.2 i)
    (smoothSpaceTime_spatial_direction hI hv a hp.1 hp.2 j)


theorem smoothSpaceTime_continuousAt (hI : IsOpen I) {u : M.Carrier → ℝ → ℝ}
    (hu : SmoothSpaceTime u (I)) (x : M.Carrier) {t : ℝ} (ht : t ∈ I) :
    ContinuousAt (fun p : M.Carrier × ℝ => u p.1 p.2) (x, t) := by
  have hmem : (chartPt x x, t) ∈ chartTarget x ×ˢ I :=
    ⟨mem_extChartAt_target x, ht⟩
  have hc : ContinuousAt (fun p : ComplexVector n × ℝ => u (chartInv x p.1) p.2)
      (chartPt x x, t) :=
    ((hu x).contDiffAt (((isOpen_extChartAt_target (I := ComplexModel n) x).prod
      hI).mem_nhds hmem)).continuousAt
  have hmap : ContinuousAt (fun p : M.Carrier × ℝ => (chartPt x p.1, p.2)) (x, t) :=
    ((continuousAt_extChartAt (I := ComplexModel n) x).comp continuousAt_fst).prodMk
      continuousAt_snd
  have hcomp := hc.comp (f := fun p : M.Carrier × ℝ => (chartPt x p.1, p.2)) hmap
  apply hcomp.congr
  have hfst : Tendsto (fun p : M.Carrier × ℝ => p.1) (𝓝 (x, t)) (𝓝 x) := continuousAt_fst
  have hnear := hfst.eventually
    ((isOpen_extChartAt_source (I := ComplexModel n) x).mem_nhds
      (mem_extChartAt_source x))
  filter_upwards [hnear] with p hp
  exact congrArg (fun y => u y p.2) ((extChartAt (ComplexModel n) x).left_inv hp)


end Yau.LeafProofs.L19Aux.LocalTime
