import Yau.Proofs.F01AActualLeviLimit
import Yau.Proofs.F01AEventualClosedJetLimits
import Yau.Proofs.F01AClosedSecondClockJet
import Yau.Proofs.F01ClosedTimeSlices
import Yau.Proofs.F01OrdinaryCharts
import Yau.LeafProofs.L17ParabolicOperatorRegularity

/-! A single retained atlas and a single diagonal sequence give all
native Levi and closed-clock limits needed by the actual core. The
queried point is allowed anywhere in a retained chart's interior. -/
noncomputable section
open Set Filter
open scoped Topology Manifold ContDiff Matrix Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs.L17ParabolicOperatorAux
variable {n : ℕ} {M : ComplexManifold n}

theorem actual_native_limits_of_retained_atlas_jets
    (a : ℕ → M.Carrier) (r : ℕ → ℝ)
    (hclosed : ∀ j, 0 < r j ∧
      Metric.closedBall (chartPt (a j) (a j)) (r j) ⊆ chartTarget (a j))
    (hcover : ∀ x : M.Carrier, ∃ j,
      x ∈ chartInv (a j) '' Metric.ball (chartPt (a j) (a j)) (r j))
    (f : ℕ → M.Carrier → ℝ → ℝ) (U : M.Carrier → ℝ → ℝ)
    (σ : ℕ → ℕ) (hσ : StrictMono σ) (hU : SmoothSpaceTime U (Ici 0))
    (hf : ∀ i, ∀ᶠ m in atTop, ContDiffOn ℝ ∞
      (fun p => f m (spaceTimeChartMap a i p).1 (spaceTimeChartMap a i p).2)
      (closedSpaceTimeChart a r i))
    (hconv : ∀ i k, TendstoUniformlyOn
      (fun m p => iteratedFDerivWithin ℝ k
        (fun q => f (σ m) (spaceTimeChartMap a i q).1 (spaceTimeChartMap a i q).2)
        (closedSpaceTimeChart a r i) p)
      (iteratedFDerivWithin ℝ k
        (fun q => U (spaceTimeChartMap a i q).1 (spaceTimeChartMap a i q).2)
        (closedSpaceTimeChart a r i)) atTop (closedSpaceTimeChart a r i)) :
    (∀ x t, 0 ≤ t →
      Tendsto (fun m => levi (fun y => f (σ m) y t) x) atTop
        (𝓝 (levi (fun y => U y t) x))) ∧
    (∀ x (k : ℕ), ∀ t ∈ Icc 0 ((k : ℝ) + 1),
      Tendsto (fun m => derivWithin (f (σ m) x) (Icc 0 ((k : ℝ) + 1)) t) atTop
        (𝓝 (derivWithin (U x) (Icc 0 ((k : ℝ) + 1)) t))) ∧
    (∀ x (k : ℕ), ∀ t ∈ Icc 0 ((k : ℝ) + 1),
      Tendsto
        (fun m => derivWithin
          (fun s => derivWithin (f (σ m) x) (Icc 0 ((k : ℝ) + 1)) s)
          (Icc 0 ((k : ℝ) + 1)) t) atTop
        (𝓝 (derivWithin
          (fun s => derivWithin (U x) (Icc 0 ((k : ℝ) + 1)) s)
          (Icc 0 ((k : ℝ) + 1)) t))) := by
  let F (j : ℕ) : ℕ → ComplexVector n × ℝ → ℝ :=
    fun m p => f (σ m) (chartInv (a j) p.1) p.2
  let V (j : ℕ) : ComplexVector n × ℝ → ℝ :=
    fun p => U (chartInv (a j) p.1) p.2
  let B (j : ℕ) : Set (ComplexVector n) :=
    Metric.ball (chartPt (a j) (a j)) (r j)
  let I (k : ℕ) : Set ℝ := Icc 0 ((k : ℝ) + 1)
  have hFO (j k : ℕ) : ∀ᶠ m in atTop, ContDiffOn ℝ ∞ (F j m) (B j ×ˢ I k) := by
    filter_upwards [hσ.tendsto_atTop.eventually (hf (Nat.pair j k))] with m hm
    have hm' : ContDiffOn ℝ ∞ (F j m)
        (Metric.closedBall (chartPt (a j) (a j)) (r j) ×ˢ I k) := by
      simpa only [F, I, spaceTimeChartMap, closedSpaceTimeChart, Nat.unpair_pair] using hm
    exact hm'.mono (prod_mono Metric.ball_subset_closedBall Subset.rfl)
  have hV (j k : ℕ) : ContDiffOn ℝ ∞ (V j) (B j ×ˢ I k) := by
    apply (hU (a j)).mono
    intro p hp
    exact ⟨(hclosed j).2 (Metric.ball_subset_closedBall hp.1), hp.2.1⟩
  have hJet (j k l : ℕ) : TendstoUniformlyOn
      (fun m p => iteratedFDerivWithin ℝ l (F j m) (B j ×ˢ I k) p)
      (iteratedFDerivWithin ℝ l (V j) (B j ×ˢ I k)) atTop (B j ×ˢ I k) := by
    apply uniform_jets_on_open_cylinder_core Metric.isOpen_ball
      Metric.ball_subset_closedBall (F j) (V j) l
    simpa only [F, V, I, spaceTimeChartMap, closedSpaceTimeChart, Nat.unpair_pair]
      using hconv (Nat.pair j k) l
  refine ⟨?_, ?_, ?_⟩
  · intro x t ht
    obtain ⟨j, z, hz, hzx⟩ := hcover x
    obtain ⟨k, hk⟩ := exists_nat_gt t
    have htI : t ∈ I k := ⟨ht, by linarith⟩
    have hLeviChart := eventual_closed_levi_limit_of_jets Metric.isOpen_ball
      (uniqueDiffOn_Icc (by positivity : (0 : ℝ) < (k : ℝ) + 1))
      (F j) (V j) (hFO j k) (hV j k) (hJet j k 2) hz htI
    let e := ordinaryChart (a j)
    have he := (ordinaryChart_contMDiffOn (a j)).mdifferentiableOn (by simp)
    have hei := (ordinaryChart_inverse_contMDiffOn (a j)).mdifferentiableOn (by simp)
    have hze : z ∈ e.source := by
      rw [ordinaryChart_source]
      exact (hclosed j).2 (Metric.ball_subset_closedBall hz)
    have hfNative : ∀ᶠ m in atTop,
        ContDiffAt ℝ 2 (inChart (e z) (fun y => f (σ m) y t))
          (chartPt (e z) (e z)) := by
      filter_upwards [hFO j k] with m hm
      apply native_contDiffAt_of_background e hei (fun y => f (σ m) y t) hze
      simpa only [e, ordinaryChart_apply, F] using
        (closed_slab_slice_jets hm Metric.isOpen_ball hz htI).1
    have huNative := smoothFn_chart_contDiffAt (smoothSpaceTime_slice hU ht) (e z)
    have hLevi := actual_native_levi_limit_of_local_chart_levi_limit e he hei hze
      (fun m y => f (σ m) y t) (fun y => U y t) hfNative huNative (by
        simpa only [e, ordinaryChart_apply, F, V] using hLeviChart)
    simpa only [e, ordinaryChart_apply, hzx] using hLevi
  · intro x k t ht
    obtain ⟨j, z, hz, hzx⟩ := hcover x
    have hTime := eventual_closed_time_derivative_limit_of_jets Metric.isOpen_ball
      (uniqueDiffOn_Icc (by positivity : (0 : ℝ) < (k : ℝ) + 1))
      (F j) (V j) (hFO j k) (hV j k) (hJet j k 1) hz ht
    simpa only [F, V, I, hzx] using hTime
  · intro x k t ht
    obtain ⟨j, z, hz, hzx⟩ := hcover x
    have hTime := eventual_closed_second_clock_derivative_limit_of_jets Metric.isOpen_ball
      (uniqueDiffOn_Icc (by positivity : (0 : ℝ) < (k : ℝ) + 1))
      (F j) (V j) (hFO j k) (hV j k) (hJet j k 2) hz ht
    simpa only [F, V, I, hzx] using hTime

end Yau.NodeProofs.F01Aux
