import Yau.Proofs.F01ABufferedOriginalAtlas
import Yau.Proofs.F01AEventualJetBudgets
import Yau.Proofs.F01GlobalPotentialCompactness

/-! Compactness on the previously fixed buffered original atlas. Every
orderwise estimate refers to these same a/r, and one diagonal subsequence
and one potential work on all closed charts and all nonnegative horizons. -/
noncomputable section
open Set Filter
open scoped Topology Manifold ContDiff NNReal
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ}

theorem global_potential_of_buffered_orderwise_closed_chart_bounds
    (M : ComplexManifold n) (a : ℕ → M.Carrier) (r : ℕ → ℝ)
    (hbuffer : ∀ j, 0 < r j ∧ 64 * r j ≤ 1 ∧
      Metric.closedBall (chartPt (a j) (a j)) (64 * r j) ⊆ chartTarget (a j))
    (hcover : ∀ x : M.Carrier, ∃ j,
      x ∈ chartInv (a j) '' Metric.ball (chartPt (a j) (a j)) (r j))
    (f : ℕ → M.Carrier → ℝ → ℝ)
    (hf0 : ∀ m x, f m x 0 = 0)
    (hsmooth : ∀ i, ∃ N : ℕ, ∀ m, N ≤ m → ContDiffOn ℝ ∞
      (fun p => f m (spaceTimeChartMap a i p).1 (spaceTimeChartMap a i p).2)
      (closedSpaceTimeChart a r i))
    (hbounds : ∀ i k, ∃ N : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ m, N ≤ m →
      ∀ p ∈ closedSpaceTimeChart a r i,
        ‖iteratedFDerivWithin ℝ k
          (fun q => f m (spaceTimeChartMap a i q).1 (spaceTimeChartMap a i q).2)
          (closedSpaceTimeChart a r i) p‖ ≤ B) :
    ∃ U : M.Carrier → ℝ → ℝ, ∃ σ : ℕ → ℕ, StrictMono σ ∧
      SmoothSpaceTime U (Ici 0) ∧ (∀ x, U x 0 = 0) ∧
      (∀ x t, 0 ≤ t → Tendsto (fun m => f (σ m) x t) atTop (𝓝 (U x t))) ∧
      ∀ i k, TendstoUniformlyOn
        (fun m p => iteratedFDerivWithin ℝ k
          (fun q => f (σ m) (spaceTimeChartMap a i q).1 (spaceTimeChartMap a i q).2)
          (closedSpaceTimeChart a r i) p)
        (iteratedFDerivWithin ℝ k
          (fun q => U (spaceTimeChartMap a i q).1 (spaceTimeChartMap a i q).2)
          (closedSpaceTimeChart a r i)) atTop (closedSpaceTimeChart a r i) := by
  classical
  have hclosed (j : ℕ) : Metric.closedBall (chartPt (a j) (a j)) (r j) ⊆ chartTarget (a j) :=
    (Metric.closedBall_subset_closedBall (by nlinarith [(hbuffer j).1])).trans (hbuffer j).2.2
  have hconvex (i : ℕ) : Convex ℝ (closedSpaceTimeChart a r i) :=
    (convex_closedBall _ _).prod (convex_Icc _ _)
  have hcompact (i : ℕ) : IsCompact (closedSpaceTimeChart a r i) :=
    (isCompact_closedBall _ _).prod isCompact_Icc
  have hUnique (i : ℕ) : UniqueDiffOn ℝ (closedSpaceTimeChart a r i) := by
    have hball : UniqueDiffOn ℝ
        (Metric.closedBall (chartPt (a (Nat.unpair i).1) (a (Nat.unpair i).1))
          (r (Nat.unpair i).1)) := by
      apply uniqueDiffOn_convex (convex_closedBall _ _)
      refine ⟨chartPt (a (Nat.unpair i).1) (a (Nat.unpair i).1), ?_⟩
      apply mem_interior_iff_mem_nhds.mpr
      exact Filter.mem_of_superset (Metric.ball_mem_nhds _ (hbuffer (Nat.unpair i).1).1)
        Metric.ball_subset_closedBall
    exact hball.prod (uniqueDiffOn_Icc (by positivity))
  choose N hN using hsmooth
  have hBudgets (i : ℕ) : ∃ C : ℕ → ℝ, (∀ k, 0 < C k) ∧ ∀ k m, N i ≤ m →
      ∀ p ∈ closedSpaceTimeChart a r i,
        ‖iteratedFDerivWithin ℝ k
          (fun q => f m (spaceTimeChartMap a i q).1 (spaceTimeChartMap a i q).2)
          (closedSpaceTimeChart a r i) p‖ ≤ C k :=
    common_threshold_jet_budgets_of_orderwise_thresholds
      (hcompact i) (hUnique i)
      (fun m q => f m (spaceTimeChartMap a i q).1 (spaceTimeChartMap a i q).2)
      (N i) (hN i) (hbounds i)
  choose C hC hEstimate using hBudgets
  let Cnn : ℕ → ℕ → ℝ≥0 := fun i k => ⟨C i k, (hC i k).le⟩
  have hinto (i : ℕ) (p : ComplexVector n × ℝ) (hp : p ∈ closedSpaceTimeChart a r i) :
      spaceTimeChartMap a i p ∈ (univ : Set M.Carrier) ×ˢ Ici 0 := ⟨mem_univ _, hp.2.1⟩
  have hcoverDomain (y : M.Carrier × ℝ) (hy : y ∈ (univ : Set M.Carrier) ×ˢ Ici 0) :
      ∃ i p, p ∈ closedSpaceTimeChart a r i ∧ spaceTimeChartMap a i p = y := by
    obtain ⟨j, z, hz, hzy⟩ := hcover y.1
    obtain ⟨k, hk⟩ := exists_nat_gt y.2
    refine ⟨Nat.pair j k, (z, y.2), ?_, ?_⟩
    · simpa only [closedSpaceTimeChart, Nat.unpair_pair] using
        (show (z, y.2) ∈ Metric.closedBall (chartPt (a j) (a j)) (r j) ×ˢ Icc 0 ((k : ℝ) + 1) from
          ⟨Metric.ball_subset_closedBall hz, hy.2, by linarith⟩)
    · have he : (chartInv (a j) z, y.2) = y := Prod.ext hzy rfl
      simpa only [spaceTimeChartMap, Nat.unpair_pair] using he
  obtain ⟨g, σ, hσ, hpoint, hlocal, hconv⟩ := eventual_chart_smooth_limit
    ((univ : Set M.Carrier) ×ˢ Ici 0) (closedSpaceTimeChart a r) (spaceTimeChartMap a)
    hinto hcoverDomain hconvex hcompact hUnique N
    (fun m y => f m y.1 y.2) (fun m i hm => hN i m hm) Cnn
    (fun i k m hm p hp => hEstimate i k m hm p hp)
  let U : M.Carrier → ℝ → ℝ := fun x t => g (x, t)
  have hUlocal (j k : ℕ) : ContDiffOn ℝ ∞
      (fun p : ComplexVector n × ℝ => U (chartInv (a j) p.1) p.2)
      (Metric.closedBall (chartPt (a j) (a j)) (r j) ×ˢ Icc 0 ((k : ℝ) + 1)) := by
    simpa only [U, spaceTimeChartMap, closedSpaceTimeChart, Nat.unpair_pair] using
      hlocal (Nat.pair j k)
  have hU : SmoothSpaceTime U (Ici 0) := by
    apply smoothSpaceTime_of_holomorphic_cover U (Ici 0)
      (fun j => ordinaryChart (a j))
      (fun j => (ordinaryChart_inverse_contMDiffOn (a j)).mdifferentiableOn (by simp))
      (fun j => Metric.ball (chartPt (a j) (a j)) (r j)) (fun _ => Metric.isOpen_ball)
    · intro j
      rw [ordinaryChart_source]
      exact Metric.ball_subset_closedBall.trans (hclosed j)
    · intro y
      obtain ⟨j, w, hw, hwy⟩ := hcover y
      exact ⟨j, w, hw, (ordinaryChart_apply (a j) w).trans hwy⟩
    · intro j
      apply contDiffOn_nonnegative_time_of_closed_slabs
      intro k
      simpa only [ordinaryChart_apply] using
        (hUlocal j k).mono (prod_mono Metric.ball_subset_closedBall Subset.rfl)
  have hpointU (x : M.Carrier) (t : ℝ) (ht : 0 ≤ t) :
      Tendsto (fun m => f (σ m) x t) atTop (𝓝 (U x t)) := hpoint (x, t) ⟨mem_univ _, ht⟩
  refine ⟨U, σ, hσ, hU, ?_, hpointU, hconv⟩
  intro x
  have hz : Tendsto (fun m => f (σ m) x 0) atTop (𝓝 (0 : ℝ)) := by
    simpa only [hf0] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  exact tendsto_nhds_unique (hpointU x 0 le_rfl) hz

theorem exists_buffered_global_potential_from_orderwise_closed_chart_bounds
    (M : ComplexManifold n) :
    ∃ (a : ℕ → M.Carrier) (r : ℕ → ℝ),
      (∀ j, 0 < r j ∧ 64 * r j ≤ 1 ∧
        Metric.closedBall (chartPt (a j) (a j)) (64 * r j) ⊆ chartTarget (a j)) ∧
      (∀ j, IsCompact (chartInv (a j) ''
        Metric.closedBall (chartPt (a j) (a j)) (64 * r j))) ∧
      (∀ x : M.Carrier, ∃ j,
        x ∈ chartInv (a j) '' Metric.ball (chartPt (a j) (a j)) (r j)) ∧
      ∀ f : ℕ → M.Carrier → ℝ → ℝ,
        (∀ m x, f m x 0 = 0) →
        (∀ i, ∃ N : ℕ, ∀ m, N ≤ m → ContDiffOn ℝ ∞
          (fun p => f m (spaceTimeChartMap a i p).1 (spaceTimeChartMap a i p).2)
          (closedSpaceTimeChart a r i)) →
        (∀ i k, ∃ N : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ m, N ≤ m →
          ∀ p ∈ closedSpaceTimeChart a r i,
            ‖iteratedFDerivWithin ℝ k
              (fun q => f m (spaceTimeChartMap a i q).1 (spaceTimeChartMap a i q).2)
              (closedSpaceTimeChart a r i) p‖ ≤ B) →
        ∃ U : M.Carrier → ℝ → ℝ, ∃ σ : ℕ → ℕ, StrictMono σ ∧
          SmoothSpaceTime U (Ici 0) ∧ (∀ x, U x 0 = 0) ∧
          (∀ x t, 0 ≤ t → Tendsto (fun m => f (σ m) x t) atTop (𝓝 (U x t))) ∧
          ∀ i k, TendstoUniformlyOn
            (fun m p => iteratedFDerivWithin ℝ k
              (fun q => f (σ m) (spaceTimeChartMap a i q).1 (spaceTimeChartMap a i q).2)
              (closedSpaceTimeChart a r i) p)
            (iteratedFDerivWithin ℝ k
              (fun q => U (spaceTimeChartMap a i q).1 (spaceTimeChartMap a i q).2)
              (closedSpaceTimeChart a r i)) atTop (closedSpaceTimeChart a r i) := by
  obtain ⟨a, r, hbuffer, hcompact, hcover⟩ := exists_buffered_countable_original_atlas M
  exact ⟨a, r, hbuffer, hcompact, hcover,
    global_potential_of_buffered_orderwise_closed_chart_bounds M a r hbuffer hcover⟩

end Yau.NodeProofs.F01Aux
