import Yau.LeafProofs.L17LocalizedSchauderTransport

open Set Metric Filter
open scoped Topology Classical
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17LocalizedSchauderAux
open Yau.LeafProofs.L17Aux Yau.LeafProofs.L17HolderAux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

/-- Transport an already supported scalar without multiplying a second cutoff. -/
def rawLocalizedTerm (P : UniformChartPartition g) (T : ℝ) (p : P.centers)
    (v : ComplexVector n × Time T → ℝ) (q : Cylinder M T) : ℝ :=
  if q.1 ∈ P.charts.chart p '' closedBall 0 P.radius then v ((P.charts.chart p).symm q.1,q.2) else 0

theorem rawLocalizedTerm_zero_of_not_cover (P : UniformChartPartition g) (T : ℝ) (p : P.centers)
    (v : ComplexVector n × Time T → ℝ) (q : Cylinder M T)
    (hx : q.1 ∉ P.charts.chart p '' closedBall 0 P.radius) : rawLocalizedTerm P T p v q = 0 :=
  if_neg hx

theorem rawLocalizedTerm_eq_of_target (P : UniformChartPartition g) (T : ℝ) (p : P.centers)
    (v : ComplexVector n × Time T → ℝ)
    (hvZero : ∀ z, z ∉ closedBall (0 : ComplexVector n) P.radius → ∀ t, v (z,t) = 0)
    (q : Cylinder M T) (hq : q.1 ∈ (P.charts.chart p).target) :
    rawLocalizedTerm P T p v q = v ((P.charts.chart p).symm q.1,q.2) := by
  by_cases hx : q.1 ∈ P.charts.chart p '' closedBall 0 P.radius
  · exact if_pos hx
  · rw [rawLocalizedTerm_zero_of_not_cover P T p v q hx]
    symm
    apply hvZero
    intro hz
    exact hx ⟨(P.charts.chart p).symm q.1,hz,(P.charts.chart p).right_inv hq⟩

theorem rawLocalizedTerm_continuous (P : UniformChartPartition g) (T : ℝ) (p : P.centers)
    (v : ComplexVector n × Time T → ℝ)
    (hv : ContinuousOn v (ball (0 : ComplexVector n) (2*P.radius) ×ˢ (Set.univ : Set (Time T))))
    (hvZero : ∀ z, z ∉ closedBall (0 : ComplexVector n) P.radius → ∀ t, v (z,t) = 0) :
    Continuous (rawLocalizedTerm P T p v) := by
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
    have hc : ContinuousAt (fun r : Cylinder M T => v ((P.charts.chart p).symm r.1,r.2)) q :=
      ContinuousAt.comp (f := fun r : Cylinder M T => ((P.charts.chart p).symm r.1,r.2)) hV hInner
    apply hc.congr
    filter_upwards [continuous_fst.continuousAt.eventually
      ((P.charts.chart p).open_target.mem_nhds hTarget)] with r hr
    exact (rawLocalizedTerm_eq_of_target P T p v hvZero r hr).symm
  · apply Filter.EventuallyEq.continuousAt (y := (0 : ℝ))
    filter_upwards [continuous_fst.continuousAt.eventually
      ((cutoff_cover_isCompact P p).isClosed.isOpen_compl.mem_nhds hx)] with r hr
    exact rawLocalizedTerm_zero_of_not_cover P T p v r hr

theorem rawLocalizedTerm_abs_le (P : UniformChartPartition g) (T : ℝ) (p : P.centers)
    (v : ComplexVector n × Time T → ℝ) {A : ℝ} (hA : 0 ≤ A)
    (hv : ∀ z ∈ ball (0 : ComplexVector n) (2*P.radius), ∀ t, |v (z,t)| ≤ A)
    (q : Cylinder M T) : |rawLocalizedTerm P T p v q| ≤ A := by
  by_cases hx : q.1 ∈ P.charts.chart p '' closedBall 0 P.radius
  · rw [rawLocalizedTerm,if_pos hx]
    have hInverse := (inverseChart_mem_of_cover P p hx).2
    exact hv _ (mem_ball.mpr (lt_of_le_of_lt (mem_closedBall.mp hInverse)
      (by have := P.radius_pos; linarith))) q.2
  · rw [rawLocalizedTerm_zero_of_not_cover P T p v q hx,abs_zero]
    exact hA

end Yau.LeafProofs.L17LocalizedSchauderAux
