import Yau.LeafProofs.L17LocalizedSchauderHolderSum

open Set Metric Filter
open scoped Topology Classical
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17LocalizedSchauderAux
open Yau.LeafProofs.L17Aux Yau.LeafProofs.L17HolderAux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

theorem localization_tsupport_subset (P : UniformChartPartition g) (p : P.centers) :
    tsupport (P.localization p) ⊆ P.charts.chart p '' closedBall 0 P.radius :=
  (P.charts.chartLocalization_properties p P.radius_pos P.radius_lt).2.2

theorem chart_closedBall_source (P : UniformChartPartition g) (p : P.centers) :
    closedBall (0 : ComplexVector n) P.radius ⊆ (P.charts.chart p).source :=
  fun z hz => P.charts.closedBall_source p ((closedBall_subset_closedBall P.radius_lt.le) hz)

theorem cutoff_cover_isCompact (P : UniformChartPartition g) (p : P.centers) :
    IsCompact (P.charts.chart p '' closedBall 0 P.radius) :=
  (isCompact_closedBall (0 : ComplexVector n) P.radius).image_of_continuousOn
    ((P.charts.chart p).continuousOn.mono (chart_closedBall_source P p))

theorem localization_zero_of_not_cover (P : UniformChartPartition g) (p : P.centers)
    {x : M.Carrier} (hx : x ∉ P.charts.chart p '' closedBall 0 P.radius) : P.localization p x = 0 :=
  image_eq_zero_of_notMem_tsupport (fun h => hx (localization_tsupport_subset P p h))

theorem inverseChart_mem_of_cover (P : UniformChartPartition g) (p : P.centers)
    {x : M.Carrier} (hx : x ∈ P.charts.chart p '' closedBall 0 P.radius) :
    x ∈ (P.charts.chart p).target ∧ (P.charts.chart p).symm x ∈ closedBall (0 : ComplexVector n) P.radius := by
  obtain ⟨z,hz,rfl⟩ := hx
  exact ⟨(P.charts.chart p).map_source (chart_closedBall_source P p hz),by
    rw [(P.charts.chart p).left_inv (chart_closedBall_source P p hz)]
    exact hz⟩

theorem localization_continuous (P : UniformChartPartition g) (p : P.centers) :
    Continuous (P.localization p) := by
  let := L12Aux.manifold_realSmooth M
  exact (L18Aux.contMDiff_real_of_smoothFn (P.localization_smooth p)).continuous

def localizedTerm (P : UniformChartPartition g) (T : ℝ) (p : P.centers)
    (v : ComplexVector n × Time T → ℝ) (q : Cylinder M T) : ℝ :=
  P.localization p q.1*v ((P.charts.chart p).symm q.1,q.2)

theorem localizedTerm_eq_formula (P : UniformChartPartition g) (T : ℝ) (p : P.centers)
    (v : ComplexVector n × Time T → ℝ) (q : Cylinder M T) :
    localizedTerm P T p v q = if q.1 ∈ (P.charts.chart p).target then
      P.localization p q.1*v ((P.charts.chart p).symm q.1,q.2) else 0 := by
  classical
  by_cases hx : q.1 ∈ (P.charts.chart p).target
  · simp only [localizedTerm,if_pos hx]
  · have hCover : q.1 ∉ P.charts.chart p '' closedBall 0 P.radius :=
      fun h => hx (inverseChart_mem_of_cover P p h).1
    simp only [localizedTerm,if_neg hx,localization_zero_of_not_cover P p hCover,zero_mul]

theorem localizedTerm_zero_of_not_cover (P : UniformChartPartition g) (T : ℝ) (p : P.centers)
    (v : ComplexVector n × Time T → ℝ) (q : Cylinder M T)
    (hx : q.1 ∉ P.charts.chart p '' closedBall 0 P.radius) : localizedTerm P T p v q = 0 := by
  rw [localizedTerm,localization_zero_of_not_cover P p hx,zero_mul]

theorem localizedTerm_continuous (P : UniformChartPartition g) (T : ℝ) (p : P.centers)
    (v : ComplexVector n × Time T → ℝ)
    (hv : ContinuousOn v (ball (0 : ComplexVector n) (2*P.radius) ×ˢ (Set.univ : Set (Time T)))) :
    Continuous (localizedTerm P T p v) := by
  rw [continuous_iff_continuousAt]
  intro q
  by_cases hx : q.1 ∈ P.charts.chart p '' closedBall 0 P.radius
  · obtain ⟨hTarget,hInverse⟩ := inverseChart_mem_of_cover P p hx
    have hz : (P.charts.chart p).symm q.1 ∈ ball (0 : ComplexVector n) (2*P.radius) :=
      mem_ball.mpr (lt_of_le_of_lt (mem_closedBall.mp hInverse) (by have := P.radius_pos; linarith))
    have hInv : ContinuousAt (P.charts.chart p).symm q.1 := (P.charts.chart p).symm.continuousOn.continuousAt
      ((P.charts.chart p).open_target.mem_nhds hTarget)
    have hOpen : IsOpen (ball (0 : ComplexVector n) (2*P.radius) ×ˢ (Set.univ : Set (Time T))) :=
      isOpen_ball.prod isOpen_univ
    have hV : ContinuousAt v ((P.charts.chart p).symm q.1,q.2) :=
      hv.continuousAt (hOpen.mem_nhds ⟨hz,mem_univ _⟩)
    have hInner : ContinuousAt (fun r : Cylinder M T => ((P.charts.chart p).symm r.1,r.2)) q :=
      (hInv.comp continuousAt_fst).prodMk continuousAt_snd
    exact ((localization_continuous P p).continuousAt.comp continuousAt_fst).mul
      (ContinuousAt.comp (f := fun r : Cylinder M T => ((P.charts.chart p).symm r.1,r.2)) hV hInner)
  · apply Filter.EventuallyEq.continuousAt (y := (0 : ℝ))
    filter_upwards [continuous_fst.continuousAt.eventually
      ((cutoff_cover_isCompact P p).isClosed.isOpen_compl.mem_nhds hx)] with r hr
    exact localizedTerm_zero_of_not_cover P T p v r hr

theorem localizedTerm_initial (P : UniformChartPartition g) (T : ℝ) (hT : 0 ≤ T) (p : P.centers)
    (v : ComplexVector n × Time T → ℝ)
    (hInitial : ∀ z ∈ ball (0 : ComplexVector n) (2*P.radius), v (z,⟨0,⟨le_rfl,hT⟩⟩) = 0)
    (x : M.Carrier) : localizedTerm P T p v (x,⟨0,⟨le_rfl,hT⟩⟩) = 0 := by
  by_cases hx : x ∈ P.charts.chart p '' closedBall 0 P.radius
  · have hz := (inverseChart_mem_of_cover P p hx).2
    have hz' : (P.charts.chart p).symm x ∈ ball (0 : ComplexVector n) (2*P.radius) :=
      mem_ball.mpr (lt_of_le_of_lt (mem_closedBall.mp hz) (by have := P.radius_pos; linarith))
    rw [localizedTerm,hInitial _ hz',mul_zero]
  · exact localizedTerm_zero_of_not_cover P T p v _ hx

end Yau.LeafProofs.L17LocalizedSchauderAux
