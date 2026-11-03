import Yau.Proofs.D04AtlasGlueVolume

open MeasureTheory Filter Set
open scoped Topology Manifold ENNReal Matrix

noncomputable section

namespace Yau.Proofs.D04AtlasGlueAux

open Yau Yau.Blueprint

variable {n : ℕ} {M : ComplexManifold n}

/-- An inner coordinate ball and a larger coordinate ball in the same
original chart. The closed inner image supplies compact covering pieces. -/
structure ChartBall (M : ComplexManifold n) where
  center : M.Carrier
  radius : ℝ
  radius_pos : 0 < radius
  closed_triple_subset : Metric.closedBall (chartPt center center) (3 * radius) ⊆
    chartTarget center

namespace ChartBall

def inner (B : ChartBall M) : Set M.Carrier :=
  chartInv B.center '' Metric.ball (chartPt B.center B.center) B.radius

def core (B : ChartBall M) : Set M.Carrier :=
  chartInv B.center '' Metric.closedBall (chartPt B.center B.center) B.radius

def outer (B : ChartBall M) : Set M.Carrier :=
  chartInv B.center '' Metric.ball (chartPt B.center B.center) (2 * B.radius)

theorem closed_inner_subset_target (B : ChartBall M) :
    Metric.closedBall (chartPt B.center B.center) B.radius ⊆ chartTarget B.center :=
  (Metric.closedBall_subset_closedBall (by linarith [B.radius_pos])).trans B.closed_triple_subset

theorem inner_subset_target (B : ChartBall M) :
    Metric.ball (chartPt B.center B.center) B.radius ⊆ chartTarget B.center :=
  Metric.ball_subset_closedBall.trans B.closed_inner_subset_target

theorem outer_subset_target (B : ChartBall M) :
    Metric.ball (chartPt B.center B.center) (2 * B.radius) ⊆ chartTarget B.center :=
  (Metric.ball_subset_closedBall.trans
    (Metric.closedBall_subset_closedBall (by linarith [B.radius_pos]))).trans B.closed_triple_subset

theorem isOpen_inner (B : ChartBall M) : IsOpen B.inner := by
  change IsOpen ((extChartAt (ComplexModel n) B.center).symm ''
    Metric.ball (chartPt B.center B.center) B.radius)
  rw [(extChartAt (ComplexModel n) B.center).symm_image_eq_source_inter_preimage
    B.inner_subset_target]
  exact isOpen_extChartAt_preimage' (I := ComplexModel n) B.center Metric.isOpen_ball

theorem isOpen_outer (B : ChartBall M) : IsOpen B.outer := by
  change IsOpen ((extChartAt (ComplexModel n) B.center).symm ''
    Metric.ball (chartPt B.center B.center) (2 * B.radius))
  rw [(extChartAt (ComplexModel n) B.center).symm_image_eq_source_inter_preimage
    B.outer_subset_target]
  exact isOpen_extChartAt_preimage' (I := ComplexModel n) B.center Metric.isOpen_ball

theorem isCompact_core (B : ChartBall M) : IsCompact B.core :=
  (isCompact_closedBall _ _).image_of_continuousOn
    ((continuousOn_extChartAt_symm (I := ComplexModel n) B.center).mono
      B.closed_inner_subset_target)

theorem inner_subset_core (B : ChartBall M) : B.inner ⊆ B.core :=
  Set.image_mono Metric.ball_subset_closedBall

theorem core_subset_outer (B : ChartBall M) : B.core ⊆ B.outer :=
  Set.image_mono (Metric.closedBall_subset_ball (by linarith [B.radius_pos]))

theorem closure_inner_subset_core (B : ChartBall M) : closure B.inner ⊆ B.core :=
  closure_minimal B.inner_subset_core B.isCompact_core.isClosed

theorem center_mem_inner (B : ChartBall M) : B.center ∈ B.inner := by
  refine ⟨chartPt B.center B.center, Metric.mem_ball_self B.radius_pos, ?_⟩
  exact (extChartAt (ComplexModel n) B.center).left_inv (mem_extChartAt_source B.center)

end ChartBall

theorem exists_chartBall (a : M.Carrier) : ∃ B : ChartBall M, B.center = a := by
  obtain ⟨r, hr, hrt⟩ := Metric.mem_nhds_iff.mp
    ((isOpen_extChartAt_target (I := ComplexModel n) a).mem_nhds
      (mem_extChartAt_target a))
  refine ⟨⟨a, r / 4, by positivity, ?_⟩, rfl⟩
  exact (Metric.closedBall_subset_ball (by linarith)).trans hrt

/-- Second countability gives one sequence of inner balls covering the whole
manifold, while retaining their compact cores and larger original charts. -/
theorem exists_countable_chartBalls (M : ComplexManifold n) :
    ∃ B : ℕ → ChartBall M, (⋃ i, (B i).inner) = univ := by
  classical
  choose B hB using (fun a : M.Carrier => exists_chartBall a)
  obtain ⟨S, hS, hcover⟩ := isLindelof_univ.elim_countable_subcover
    (fun a : M.Carrier => (B a).inner) (fun a => (B a).isOpen_inner)
    (by
      intro x _
      exact mem_iUnion.mpr ⟨x, by simpa only [hB x] using (B x).center_mem_inner⟩)
  have hSne : S.Nonempty := by
    obtain ⟨p⟩ := (inferInstance : Nonempty M.Carrier)
    obtain ⟨a, ha⟩ := mem_iUnion.mp (hcover (mem_univ p))
    obtain ⟨haS, _⟩ := mem_iUnion.mp ha
    exact ⟨a, haS⟩
  obtain ⟨c, hc⟩ := hS.exists_eq_range hSne
  refine ⟨fun i => B (c i), eq_univ_of_forall ?_⟩
  intro p
  obtain ⟨a, ha⟩ := mem_iUnion.mp (hcover (mem_univ p))
  obtain ⟨haS, hp⟩ := mem_iUnion.mp ha
  rw [hc] at haS
  obtain ⟨i, rfl⟩ := haS
  exact mem_iUnion.mpr ⟨i, hp⟩

/-- Every compact is covered by finitely many of the retained inner balls. -/
theorem finite_chartBall_cover (B : ℕ → ChartBall M)
    (hB : (⋃ i, (B i).inner) = univ) {K : Set M.Carrier} (hK : IsCompact K) :
    ∃ I : Finset ℕ, K ⊆ ⋃ i ∈ I, (B i).inner := by
  obtain ⟨I, hcover⟩ := hK.elim_finite_subcover
    (fun i => (B i).inner) (fun i => (B i).isOpen_inner)
    (by rw [hB]; exact subset_univ K)
  exact ⟨I, hcover⟩

/-- A closed affine disc in an arbitrary original chart lies in the
connected component of its center inside that chart target. -/
theorem closed_disc_subset_chart_component (a : M.Carrier)
    (z w : ComplexVector n)
    (hdisc : ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → z + ζ • w ∈ chartTarget a) :
    IsOpen (connectedComponentIn (chartTarget a) z) ∧
      IsConnected (connectedComponentIn (chartTarget a) z) ∧
      ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → z + ζ • w ∈ connectedComponentIn (chartTarget a) z := by
  have hz : z ∈ chartTarget a := by simpa using hdisc 0 (by simp)
  let f : ℂ → ComplexVector n := fun ζ => z + ζ • w
  have hf : Continuous f := continuous_const.add (continuous_id.smul continuous_const)
  have hclosed : IsPreconnected (f '' Metric.closedBall 0 1) :=
    (convex_closedBall (0 : ℂ) (1 : ℝ)).isPreconnected.image f hf.continuousOn
  have hzimage : z ∈ f '' Metric.closedBall 0 1 := by
    exact ⟨0, by simp, by simp [f]⟩
  have himage : f '' Metric.closedBall 0 1 ⊆ chartTarget a := by
    rintro y ⟨ζ, hζ, rfl⟩
    exact hdisc ζ (by simpa using hζ)
  refine ⟨(isOpen_extChartAt_target (I := ComplexModel n) a).connectedComponentIn,
    isConnected_connectedComponentIn_iff.mpr hz, ?_⟩
  intro ζ hζ
  exact hclosed.subset_connectedComponentIn hzimage himage ⟨ζ, by simpa using hζ, rfl⟩

end Yau.Proofs.D04AtlasGlueAux
