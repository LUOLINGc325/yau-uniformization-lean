import Yau.Proofs.C01ScalarDistanceGrowth
import Yau.LeafProofs.L12

/-! The first-exit sphere uses only the original complete metric.
Its positive-time distance minimum is attained by compactness of that
sphere; no positive-time completeness is used. -/

noncomputable section

open scoped Manifold Topology ContDiff Matrix ComplexOrder

namespace Yau.NodeProofs.C01Aux

open Yau Yau.Blueprint
open Yau.LeafProofs.L12Aux Yau.LeafProofs.L23Aux

variable {n : ℕ} {M : ComplexManifold n}

def initialDistanceSphere (g : SmoothMetric M) (o : M.Carrier) (L : ℝ) : Set M.Carrier :=
  {x | inducedDistance g.form o x = L}

def exitDistanceProfile (g : SmoothMetric M) (k : HermitianField M)
    (o : M.Carrier) (L : ℝ) : ℝ :=
  sInf ((inducedDistance k o) '' initialDistanceSphere g o L)

theorem initial_distance_unbounded (g : SmoothMetric M) (o : M.Carrier) (L : ℝ) :
    ∃ y : M.Carrier, L ≤ inducedDistance g.form o y := by
  by_contra h
  push Not at h
  have hsub : (Set.univ : Set M.Carrier) ⊆ {y | inducedDistance g.form o y ≤ L} :=
    fun y _ => (h y).le
  exact noncompact_univ M.Carrier
    ((isCompact_inducedDistance_sublevel g o L).of_isClosed_subset isClosed_univ hsub)

theorem initialDistanceSphere_nonempty (g : SmoothMetric M) (o : M.Carrier)
    (L : ℝ) (hL : 0 ≤ L) : (initialDistanceSphere g o L).Nonempty := by
  obtain ⟨y, hy⟩ := initial_distance_unbounded g o L
  have hcontinuous : Continuous (inducedDistance g.form o) :=
    (Yau.LeafProofs.L12Aux.continuous_inducedDistance g).comp
      (continuous_const.prodMk continuous_id)
  have hbetween : L ∈ Set.Icc (inducedDistance g.form o o) (inducedDistance g.form o y) := by
    change inducedDistance g.form o o ≤ L ∧ L ≤ inducedDistance g.form o y
    rw [g.induced_distance_eq_zero.mpr rfl]
    exact ⟨hL, hy⟩
  obtain ⟨x, _, hx⟩ := isPreconnected_univ.intermediate_value
    (Set.mem_univ o) (Set.mem_univ y) hcontinuous.continuousOn hbetween
  exact ⟨x, hx⟩

theorem initialDistanceSphere_isCompact (g : SmoothMetric M) (o : M.Carrier) (L : ℝ) :
    IsCompact (initialDistanceSphere g o L) := by
  have hc : Continuous (inducedDistance g.form o) :=
    (Yau.LeafProofs.L12Aux.continuous_inducedDistance g).comp
      (continuous_const.prodMk continuous_id)
  apply (isCompact_inducedDistance_sublevel g o L).of_isClosed_subset
    (isClosed_eq hc continuous_const)
  intro x hx
  exact hx.le

theorem exitDistanceProfile_attained (g : SmoothMetric M) (k : HermitianField M)
    (hk : MetricSmooth k) (o : M.Carrier) (L : ℝ) (hL : 0 ≤ L) :
    ∃ y ∈ initialDistanceSphere g o L,
      exitDistanceProfile g k o L = inducedDistance k o y ∧
      ∀ z ∈ initialDistanceSphere g o L, inducedDistance k o y ≤ inducedDistance k o z := by
  exact (initialDistanceSphere_isCompact g o L).exists_sInf_image_eq_and_le
    (initialDistanceSphere_nonempty g o L hL)
    (Yau.LeafProofs.L23Aux.continuous_distFrom k hk o).continuousOn

theorem exitDistanceProfile_le (g : SmoothMetric M) (k : HermitianField M)
    (hk : MetricSmooth k) (o : M.Carrier) (L : ℝ) (hL : 0 ≤ L)
    (z : M.Carrier) (hz : z ∈ initialDistanceSphere g o L) :
    exitDistanceProfile g k o L ≤ inducedDistance k o z := by
  obtain ⟨y, _hy, heq, hmin⟩ := exitDistanceProfile_attained g k hk o L hL
  rw [heq]
  exact hmin z hz

theorem exitDistanceProfile_pos (g : SmoothMetric M) (k : HermitianField M)
    (hk : MetricSmooth k) (o : M.Carrier) (L : ℝ) (hL : 0 < L) :
    0 < exitDistanceProfile g k o L := by
  obtain ⟨y, hy, heq, _⟩ := exitDistanceProfile_attained g k hk o L hL.le
  rw [heq]
  have hyo : y ≠ o := by
    intro hyo
    have hyL : inducedDistance g.form o y = L := hy
    rw [hyo, g.induced_distance_eq_zero.mpr rfl] at hyL
    linarith
  letI := metricSpaceOfField k hk
  exact dist_pos.mpr (Ne.symm hyo)

theorem exitDistanceProfile_initial (g : SmoothMetric M) (o : M.Carrier)
    (L : ℝ) (hL : 0 ≤ L) : exitDistanceProfile g g.form o L = L := by
  have hk : MetricSmooth g.form := metricSmooth_of_smoothMetric g
  obtain ⟨y, hy, heq, _⟩ := exitDistanceProfile_attained g g.form hk o L hL
  exact heq.trans hy

end Yau.NodeProofs.C01Aux
