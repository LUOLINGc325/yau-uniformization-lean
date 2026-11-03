import Yau.LeafProofs.L23JointCalculus
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Compact parameter integrals preserve finite regularity; all derivatives are genuine. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff
namespace Yau.LeafProofs.L23Aux
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

theorem exists_compact_parameter_ball {U : Set E} (hU : IsOpen U) {x : E} (hx : x∈U) :
    ∃ ε : ℝ, 0<ε ∧ Metric.closedBall x ε ⊆ U := by
  obtain ⟨ε,hε,hεU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
  refine ⟨ε/2,by positivity,?_⟩
  intro y hy
  apply hεU
  exact (Metric.mem_closedBall.mp hy).trans_lt (by linarith)

theorem continuousOn_unitIntegral {F : E × ℝ → G} {U : Set E} {J : Set ℝ}
    (hU : IsOpen U) (hJ : IsOpen J) (hIJ : Set.Icc (0 : ℝ) 1 ⊆ J)
    (hF : ContinuousOn F (U ×ˢ J)) :
    ContinuousOn (fun x => ∫ u in Set.Icc (0 : ℝ) 1, F (x,u)) U := by
  intro x hx
  obtain ⟨ε,hε,hεU⟩ := exists_compact_parameter_ball hU hx
  have hsub : Metric.closedBall x ε ×ˢ Set.Icc (0 : ℝ) 1 ⊆ U ×ˢ J :=
    fun _ hp => ⟨hεU hp.1,hIJ hp.2⟩
  obtain ⟨C,hC⟩ := ((isCompact_closedBall x ε).prod (isCompact_Icc (a := (0 : ℝ)) (b := 1))).exists_bound_of_continuousOn
    (hF.mono hsub)
  have hslice {y : E} (hy : y∈U) : ContinuousOn (fun u => F (y,u)) (Set.Icc (0 : ℝ) 1) :=
    hF.comp (continuous_const.prodMk continuous_id).continuousOn (fun _ hu => ⟨hy,hIJ hu⟩)
  apply ContinuousAt.continuousWithinAt
  apply continuousAt_of_dominated (bound := fun _ : ℝ => C)
  · filter_upwards [Metric.ball_mem_nhds x hε] with y hy
    exact (hslice (hεU (Metric.ball_subset_closedBall hy))).aestronglyMeasurable measurableSet_Icc
  · filter_upwards [Metric.ball_mem_nhds x hε] with y hy
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    exact hC (y,u) ⟨Metric.ball_subset_closedBall hy,hu⟩
  · exact integrableOn_const (by simp)
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    exact (hF.continuousAt ((hU.prod hJ).mem_nhds ⟨hx,hIJ hu⟩)).comp
      (f := fun y : E => (y,u)) (continuousAt_id.prodMk continuousAt_const)

def parameterDerivative (F : E × ℝ → G) (p : E × ℝ) : E →L[ℝ] G :=
  (fderiv ℝ F p).comp ((ContinuousLinearMap.id ℝ E).prod 0)

theorem parameterDerivative_hasFDerivAt (F : E × ℝ → G) {p : E × ℝ}
    (hF : DifferentiableAt ℝ F p) :
    HasFDerivAt (fun x => F (x,p.2)) (parameterDerivative F p) p.1 := by
  exact hF.hasFDerivAt.comp p.1
    ((hasFDerivAt_id p.1).prodMk (hasFDerivAt_const p.2 p.1))

theorem parameterDerivative_contDiffOn {F : E × ℝ → G} {U : Set E} {J : Set ℝ}
    (hU : IsOpen U) (hJ : IsOpen J) (k : ℕ)
    (hF : ContDiffOn ℝ (k+1) F (U ×ˢ J)) :
    ContDiffOn ℝ k (parameterDerivative F) (U ×ˢ J) := by
  exact (hF.fderiv_of_isOpen (hU.prod hJ) (by simp)).clm_comp contDiffOn_const

theorem hasFDerivAt_unitIntegral {F : E × ℝ → G} {U : Set E} {J : Set ℝ}
    (hU : IsOpen U) (hJ : IsOpen J) (hIJ : Set.Icc (0 : ℝ) 1 ⊆ J)
    (hF : ContDiffOn ℝ 1 F (U ×ˢ J)) {x : E} (hx : x∈U) :
    HasFDerivAt (fun y => ∫ u in Set.Icc (0 : ℝ) 1, F (y,u))
      (∫ u in Set.Icc (0 : ℝ) 1, parameterDerivative F (x,u)) x := by
  obtain ⟨ε,hε,hεU⟩ := exists_compact_parameter_ball hU hx
  have hsub : Metric.closedBall x ε ×ˢ Set.Icc (0 : ℝ) 1 ⊆ U ×ˢ J :=
    fun _ hp => ⟨hεU hp.1,hIJ hp.2⟩
  have hD : ContinuousOn (parameterDerivative F) (U ×ˢ J) :=
    (parameterDerivative_contDiffOn hU hJ 0 (by simpa using hF)).continuousOn
  obtain ⟨C,hC⟩ := ((isCompact_closedBall x ε).prod (isCompact_Icc (a := (0 : ℝ)) (b := 1))).exists_bound_of_continuousOn
    (hD.mono hsub)
  have hslice {y : E} (hy : y∈U) : ContinuousOn (fun u => F (y,u)) (Set.Icc (0 : ℝ) 1) :=
    hF.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hu => ⟨hy,hIJ hu⟩)
  have hDslice : ContinuousOn (fun u => parameterDerivative F (x,u)) (Set.Icc (0 : ℝ) 1) :=
    hD.comp (continuous_const.prodMk continuous_id).continuousOn (fun _ hu => ⟨hx,hIJ hu⟩)
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (s := Metric.closedBall x ε) (bound := fun _ : ℝ => C) (Metric.closedBall_mem_nhds x hε)
  · filter_upwards [Metric.ball_mem_nhds x hε] with y hy
    exact (hslice (hεU (Metric.ball_subset_closedBall hy))).aestronglyMeasurable measurableSet_Icc
  · exact (hslice hx).integrableOn_Icc
  · exact hDslice.aestronglyMeasurable measurableSet_Icc
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    intro y hy
    exact hC (y,u) ⟨hy,hu⟩
  · exact integrableOn_const (by simp)
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    intro y hy
    exact parameterDerivative_hasFDerivAt F (p := (y,u))
      ((hF.contDiffAt ((hU.prod hJ).mem_nhds ⟨hεU hy,hIJ hu⟩)).differentiableAt_one)

theorem contDiffOn_unitIntegral {F : E × ℝ → G} {U : Set E} {J : Set ℝ}
    (hU : IsOpen U) (hJ : IsOpen J) (hIJ : Set.Icc (0 : ℝ) 1 ⊆ J) (k : ℕ)
    (hF : ContDiffOn ℝ k F (U ×ˢ J)) :
    ContDiffOn ℝ k (fun x => ∫ u in Set.Icc (0 : ℝ) 1, F (x,u)) U := by
  induction k generalizing G with
  | zero => exact (contDiffOn_zero).mpr (continuousOn_unitIntegral hU hJ hIJ hF.continuousOn)
  | succ k ih =>
      intro x hx
      apply ContDiffAt.contDiffWithinAt
      apply contDiffAt_succ_iff_hasFDerivAt.mpr
      refine ⟨fun y => ∫ u in Set.Icc (0 : ℝ) 1, parameterDerivative F (y,u),?_,?_⟩
      · exact ⟨U,hU.mem_nhds hx,fun y hy => hasFDerivAt_unitIntegral hU hJ hIJ (hF.of_le (by simp)) hy⟩
      · exact (ih (parameterDerivative_contDiffOn hU hJ k hF)).contDiffAt (hU.mem_nhds hx)

end Yau.LeafProofs.L23Aux
