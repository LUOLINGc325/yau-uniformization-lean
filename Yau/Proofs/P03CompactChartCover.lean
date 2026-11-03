import Yau.Geometry.Calculus

open scoped Manifold Topology
open Set

noncomputable section

namespace Yau.NodeProofs.P03Aux

variable {n : ℕ} {M : ComplexManifold n}

theorem compactChartBall_isCompact (a : M.Carrier) {r : ℝ}
    (hr : Metric.closedBall (chartPt a a) r ⊆ chartTarget a) :
    IsCompact (chartInv a '' Metric.closedBall (chartPt a a) r) :=
  (isCompact_closedBall _ _).image_of_continuousOn
    ((continuousOn_extChartAt_symm (I := ComplexModel n) a).mono hr)

theorem chartBall_isOpen (a : M.Carrier) {r : ℝ}
    (hr : Metric.closedBall (chartPt a a) r ⊆ chartTarget a) :
    IsOpen (chartInv a '' Metric.ball (chartPt a a) r) := by
  have heq : chartInv a '' Metric.ball (chartPt a a) r =
      (extChartAt (ComplexModel n) a).source ∩
        (chartPt a) ⁻¹' Metric.ball (chartPt a a) r := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hzt := hr (Metric.ball_subset_closedBall hz)
      refine ⟨(extChartAt (ComplexModel n) a).map_target hzt, ?_⟩
      change (extChartAt (ComplexModel n) a)
        ((extChartAt (ComplexModel n) a).symm z) ∈ Metric.ball (chartPt a a) r
      rw [(extChartAt (ComplexModel n) a).right_inv hzt]
      exact hz
    · intro hx
      exact ⟨chartPt a x, hx.2, (extChartAt (ComplexModel n) a).left_inv hx.1⟩
  rw [heq]
  exact isOpen_extChartAt_preimage' a Metric.isOpen_ball

/-- Actual compact coordinate balls have a countable selection whose open
balls cover the entire manifold. The radii and every chart are geometric
data obtained directly from the given manifold atlas. -/
theorem exists_countable_compact_chart_cover (M : ComplexManifold n) :
    ∃ (r : M.Carrier → ℝ) (T : Set M.Carrier),
      (∀ a, 0 < r a) ∧
      (∀ a, Metric.closedBall (chartPt a a) (r a) ⊆ chartTarget a) ∧
      T.Countable ∧
      (⋃ a ∈ T, chartInv a '' Metric.ball (chartPt a a) (r a)) = univ := by
  classical
  have hrad (a : M.Carrier) : ∃ r : ℝ, 0 < r ∧
      Metric.closedBall (chartPt a a) r ⊆ chartTarget a :=
    Metric.nhds_basis_closedBall.mem_iff.mp
      ((isOpen_extChartAt_target a).mem_nhds (mem_extChartAt_target a))
  choose r hr hsub using hrad
  let W : M.Carrier → Set M.Carrier := fun a =>
    chartInv a '' Metric.ball (chartPt a a) (r a)
  have hopen (a : M.Carrier) : IsOpen (W a) := chartBall_isOpen a (hsub a)
  have hcover : (⋃ a, W a) = univ := by
    apply eq_univ_iff_forall.mpr
    intro x
    apply mem_iUnion.mpr
    refine ⟨x, chartPt x x, Metric.mem_ball_self (hr x), ?_⟩
    exact (extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x)
  obtain ⟨T, hT, hTW⟩ := TopologicalSpace.isOpen_iUnion_countable W hopen
  exact ⟨r, T, hr, hsub, hT, hTW.trans hcover⟩

end Yau.NodeProofs.P03Aux
