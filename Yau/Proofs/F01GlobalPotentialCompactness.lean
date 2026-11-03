import Yau.Proofs.F01CountableSmoothnessAtlas
import Yau.Proofs.F01EventualChartSmoothLimit

/-! The actual manifold supplies a countable closed-cylinder atlas before
the approximating potentials. Eventual all-order bounds construct one
globally smooth potential and one common subsequence on all horizons. -/
noncomputable section
open Set Filter
open scoped Topology Manifold ContDiff NNReal
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}

def closedSpaceTimeChart (a : ℕ → M.Carrier) (r : ℕ → ℝ) (i : ℕ) :
    Set (ComplexVector n × ℝ) :=
  Metric.closedBall (chartPt (a (Nat.unpair i).1) (a (Nat.unpair i).1)) (r (Nat.unpair i).1) ×ˢ
    Icc 0 (((Nat.unpair i).2 : ℝ) + 1)

def spaceTimeChartMap (a : ℕ → M.Carrier) (i : ℕ) (p : ComplexVector n × ℝ) : M.Carrier × ℝ :=
  (chartInv (a (Nat.unpair i).1) p.1, p.2)

theorem exists_global_potential_compactness_atlas (M : ComplexManifold n) :
    ∃ (a : ℕ → M.Carrier) (r : ℕ → ℝ),
      (∀ j, 0 < r j ∧ Metric.closedBall (chartPt (a j) (a j)) (r j) ⊆ chartTarget (a j)) ∧
      (∀ j, IsCompact (chartInv (a j) '' Metric.closedBall (chartPt (a j) (a j)) (r j))) ∧
      ∀ (f : ℕ → M.Carrier → ℝ → ℝ) (N : ℕ → ℕ) (C : ℕ → ℕ → ℝ≥0),
        (∀ m i, N i ≤ m → ContDiffOn ℝ ∞
          (fun p => f m (spaceTimeChartMap a i p).1 (spaceTimeChartMap a i p).2)
          (closedSpaceTimeChart a r i)) →
        (∀ i k m, N i ≤ m → ∀ p ∈ closedSpaceTimeChart a r i,
          ‖iteratedFDerivWithin ℝ k
            (fun q => f m (spaceTimeChartMap a i q).1 (spaceTimeChartMap a i q).2)
            (closedSpaceTimeChart a r i) p‖ ≤ C i k) →
        ∃ U : M.Carrier → ℝ → ℝ, ∃ σ : ℕ → ℕ, StrictMono σ ∧
          SmoothSpaceTime U (Ici 0) ∧
          (∀ x t, 0 ≤ t → Tendsto (fun m => f (σ m) x t) atTop (𝓝 (U x t))) ∧
          ∀ i k, TendstoUniformlyOn
            (fun m p => iteratedFDerivWithin ℝ k
              (fun q => f (σ m) (spaceTimeChartMap a i q).1 (spaceTimeChartMap a i q).2)
              (closedSpaceTimeChart a r i) p)
            (iteratedFDerivWithin ℝ k
              (fun q => U (spaceTimeChartMap a i q).1 (spaceTimeChartMap a i q).2)
              (closedSpaceTimeChart a r i)) atTop (closedSpaceTimeChart a r i) := by
  obtain ⟨a, r, hclosed, hcompact, hcover, hsmooth⟩ := exists_countable_smoothness_atlas M
  refine ⟨a, r, hclosed, hcompact, ?_⟩
  intro f N C hf hbound
  have hconvex (i : ℕ) : Convex ℝ (closedSpaceTimeChart a r i) :=
    (convex_closedBall _ _).prod (convex_Icc _ _)
  have hcompactDomain (i : ℕ) : IsCompact (closedSpaceTimeChart a r i) :=
    (isCompact_closedBall _ _).prod isCompact_Icc
  have hUnique (i : ℕ) : UniqueDiffOn ℝ (closedSpaceTimeChart a r i) := by
    have hball : UniqueDiffOn ℝ
        (Metric.closedBall (chartPt (a (Nat.unpair i).1) (a (Nat.unpair i).1)) (r (Nat.unpair i).1)) := by
      apply uniqueDiffOn_convex (convex_closedBall _ _)
      refine ⟨chartPt (a (Nat.unpair i).1) (a (Nat.unpair i).1), ?_⟩
      apply mem_interior_iff_mem_nhds.mpr
      exact Filter.mem_of_superset (Metric.ball_mem_nhds _ (hclosed (Nat.unpair i).1).1)
        Metric.ball_subset_closedBall
    exact hball.prod (uniqueDiffOn_Icc (by positivity))
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
    hinto hcoverDomain hconvex hcompactDomain hUnique N
    (fun m y => f m y.1 y.2) hf C hbound
  let U : M.Carrier → ℝ → ℝ := fun x t => g (x, t)
  refine ⟨U, σ, hσ, ?_, (fun x t ht => hpoint (x, t) ⟨mem_univ _, ht⟩), hconv⟩
  apply hsmooth U
  intro j k
  simpa only [U, spaceTimeChartMap, closedSpaceTimeChart, Nat.unpair_pair] using
    hlocal (Nat.pair j k)

end Yau.NodeProofs.F01Aux
