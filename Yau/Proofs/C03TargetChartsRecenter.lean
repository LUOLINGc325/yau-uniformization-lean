import Yau.Proofs.C03TargetCharts

/-! Recenter the same finite atlas without changing its uniform metric constants. -/
noncomputable section
open Set
open scoped Topology ContDiff Manifold Matrix ComplexOrder
namespace Yau.Proofs.C03Aux.TargetCharts
open Yau Yau.Blueprint Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem exists_uniform_recentered_charts (g : SmoothMetric M)
    (K : Set M.Carrier) (hK : IsCompact K) :
    ∃ (I : Finset M.Carrier) (r : M.Carrier → ℝ) (d U L δstar : ℝ),
      0 < d ∧ 0 < U ∧ 0 < L ∧ 0 < δstar ∧
      ∀ p ∈ K, ∃ a ∈ I,
        p ∈ (extChartAt (ComplexModel n) a).source ∧
        ‖chartPt a p - chartPt a a‖ < r a ∧ δstar ≤ r a ∧
        ∀ δ : ℝ, 0 < δ → δ ≤ δstar →
          Metric.ball (chartPt a p) δ ⊆ chartTarget a ∧
          ∀ w ∈ Metric.ball (chartPt a p) δ,
            HermLE ((d : ℂ) • (1 : Herm n)) (hMat g.form a w) ∧
            HermLE (hMat g.form a w) ((U : ℂ) • (1 : Herm n)) ∧
            ∀ v : ComplexVector n, realMetricInChart g.form a w v v ≤ L ^ 2 * ‖v‖ ^ 2 := by
  obtain ⟨I, r, d, U, L, δstar, hd, hU, hL, hδ, hb, hcover⟩ :=
    exists_finite_metric_chart_cover g K hK
  refine ⟨I, r, d, U, L, δstar, hd, hU, hL, hδ, ?_⟩
  intro p hp
  obtain ⟨a, ha⟩ := mem_iUnion.mp (hcover hp)
  obtain ⟨haI, w, hw, hwp⟩ := mem_iUnion.mp ha
  obtain ⟨hr, hδr, htarget, hmetric⟩ := hb a haI
  have hwt : w ∈ chartTarget a := htarget
    (Metric.closedBall_subset_closedBall (by linarith) (Metric.ball_subset_closedBall hw))
  have hsrc : p ∈ (extChartAt (ComplexModel n) a).source := by
    rw [← hwp]
    exact (extChartAt (ComplexModel n) a).map_target hwt
  have hcoord : chartPt a p = w := by
    rw [← hwp]
    exact (extChartAt (ComplexModel n) a).right_inv hwt
  have hw0 : dist (chartPt a p) (chartPt a a) < r a := by
    rw [hcoord]
    exact hw
  refine ⟨a, haI, hsrc, by simpa only [dist_eq_norm] using hw0, hδr, ?_⟩
  intro δ _ hδle
  have hsub : Metric.ball (chartPt a p) δ ⊆
      Metric.closedBall (chartPt a a) (4 * r a) := by
    intro z hz
    have hz' : dist z (chartPt a p) < δ := hz
    apply Metric.mem_closedBall.mpr
    calc
      dist z (chartPt a a) ≤ dist z (chartPt a p) + dist (chartPt a p) (chartPt a a) :=
        dist_triangle _ _ _
      _ ≤ 4 * r a := by linarith
  exact ⟨hsub.trans htarget, fun z hz => hmetric z (hsub hz)⟩

end Yau.Proofs.C03Aux.TargetCharts
