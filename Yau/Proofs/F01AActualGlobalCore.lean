import Yau.Proofs.F01AActualClosedJointBudgets
import Yau.Proofs.F01ABufferedCompactnessAtlas
import Yau.Proofs.F01ARetainedAtlasJetLimits
import Yau.Proofs.F01AActualNativeCore
import Yau.Proofs.F01AActualPointData
import Yau.Proofs.F01AActualSequenceOrders
import Yau.Proofs.F01AActualSmoothComparison
import Yau.Proofs.F01OriginalApplication

/-! The actual continued approximants have uniform compact closed jets.
One diagonal subsequence constructs one potential and one native flow;
all smooth Ricci weights pass through that same sequence afterwards. -/
noncomputable section
open Set Filter
open scoped Topology Manifold ContDiff Matrix ComplexOrder Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Blueprint
variable {n : ℕ}

theorem actual_global_core_and_smooth_comparison
    (X : KahlerManifold n) (o : Pt X) (u : Pt X → ℝ)
    (hu : ControlledExhaustion X o u) (hinitial : CanonicalInitialData X o) :
    ∃ (h : Flow X) (U P ρ : STF X) (η : ℝ), 0 < η ∧
      LocalizedFlowCore X h U P ρ ∧ SmoothRicciWeightComparison X u U P η := by
  classical
  obtain ⟨Ξ, hΞ, hRic, CΞ, hGrowth⟩ := hinitial.2
  let c : ℝ := max 0 CΞ
  have hc : 0 ≤ c := le_max_left _ _
  have hFactor (x : Pt X) : 0 ≤ 1 + distFrom X.metric.form o x ^ ((3 : ℝ) / 2) :=
    add_nonneg zero_le_one (Real.rpow_nonneg (X.metric.induced_distance_nonneg o x) _)
  have hGrowth' (x : Pt X) : Ξ x ≤ c * (1 + distFrom X.metric.form o x ^ ((3 : ℝ) / 2)) :=
    (hGrowth x).trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
      (hFactor x))
  obtain ⟨L, ho, h, V, hL, hSequence⟩ :=
    exists_actual_approximation_sequence X o u hu Ξ hΞ hRic
  have hsol (m : ℕ) : NativePotentialSlab
      (approximatingMetric X.manifold X.metric.form u hu.1 o (L m) (ho m))
      ((m : ℝ) + 2) (h m) (V m) := (hSequence m).2
  let f : ℕ → STF X := fun m => ambientApproximationPotential X o u hu (L m) (ho m) (V m)
  let p : ℕ → STF X := fun m => ambientApproximationPotential X o u hu (L m) (ho m)
    (flowLogDetRatio (approximatingMetric X.manifold X.metric.form u hu.1 o (L m) (ho m)) (h m))
  obtain ⟨a, r, hbuffer, hcompact, hcover⟩ := exists_buffered_countable_original_atlas X.manifold
  have hLocal (i : ℕ) := actual_original_chart_closed_joint_budgets
    X o u hu Ξ hΞ hRic hc hGrowth' L ho h V hL hsol
    (a (Nat.unpair i).1) (hbuffer (Nat.unpair i).1).1
    (hbuffer (Nat.unpair i).1).2.1 (hbuffer (Nat.unpair i).1).2.2
    (le_add_of_nonneg_left (Nat.cast_nonneg (Nat.unpair i).2) : 1 ≤ ((Nat.unpair i).2 : ℝ) + 1)
  have hSmooth (i : ℕ) : ∀ᶠ m in atTop, ContDiffOn ℝ ∞
      (fun q => f m (spaceTimeChartMap a i q).1 (spaceTimeChartMap a i q).2)
      (closedSpaceTimeChart a r i) := by
    simpa only [f, spaceTimeChartMap, closedSpaceTimeChart] using (hLocal i).1
  have hBounds (i k : ℕ) : ∃ N : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ m : ℕ, N ≤ m →
      ∀ q ∈ closedSpaceTimeChart a r i,
        ‖iteratedFDerivWithin ℝ k
          (fun w => f m (spaceTimeChartMap a i w).1 (spaceTimeChartMap a i w).2)
          (closedSpaceTimeChart a r i) q‖ ≤ B := by
    simpa only [f, spaceTimeChartMap, closedSpaceTimeChart] using (hLocal i).2 k
  have hf0 (m : ℕ) (x : Pt X) : f m x 0 = 0 :=
    ambientApproximationPotential_initial X o u hu (L m) (ho m) (V m) (hsol m).2.2.2.1 x
  obtain ⟨U, σ, hσ, hU, hU0, hPoint, hJets⟩ :=
    global_potential_of_buffered_orderwise_closed_chart_bounds X.manifold a r hbuffer hcover f hf0
      (fun i => eventually_atTop.mp (hSmooth i)) hBounds
  have hclosed (j : ℕ) : 0 < r j ∧
      Metric.closedBall (chartPt (a j) (a j)) (r j) ⊆ chartTarget (a j) :=
    ⟨(hbuffer j).1,
      (Metric.closedBall_subset_closedBall (by linarith [(hbuffer j).1])).trans (hbuffer j).2.2⟩
  obtain ⟨hLevi, hFirst, hSecond⟩ := actual_native_limits_of_retained_atlas_jets
    a r hclosed hcover f U σ hσ hU hSmooth hJets
  have hOriginalOrders := actual_approximation_eventual_native_orders
    X o u hu Ξ hΞ hRic hc hGrowth' L ho h V hL hsol
  have hOrders (x : Pt X) (t : ℝ) (ht : 0 ≤ t) : ∃ ell : ℝ, 0 < ell ∧ ∃ R : ℝ,
      (∀ᶠ m in atTop,
        (nativePotentialMatrix X.metric.form (f (σ m)) t x -
          (ell : ℂ) • gMat X.metric.form x).PosSemidef) ∧
      (∀ᶠ m in atTop,
        ((Real.exp (2 * R / L (σ m)) : ℂ) • gMat X.metric.form x -
          nativePotentialMatrix X.metric.form (f (σ m)) t x).PosSemidef) := by
    obtain ⟨ell, hell, R, hlo, hhi⟩ := hOriginalOrders x t ht
    exact ⟨ell, hell, R, hσ.tendsto_atTop.eventually hlo, hσ.tendsto_atTop.eventually hhi⟩
  obtain ⟨a0, ha0, hFinitePDE, hFiniteLog, hPCap, hSecondCap⟩ :=
    actual_approximation_point_data X o u hu L ho h V hL hsol
  obtain ⟨hGlobal, hCore, hPPoint⟩ := exists_native_core_of_actual_same_sequence_limits
    X L f p U σ hσ hL hU hU0 hLevi hOrders hFirst hSecond
    (fun x k => hσ.tendsto_atTop.eventually (hFinitePDE x k))
    (fun x t ht => hσ.tendsto_atTop.eventually (hFiniteLog x t ht))
    (fun x t ht => ⟨a0 * t, hσ.tendsto_atTop.eventually (hPCap x t ht)⟩)
    (fun x k t ht => ⟨a0, hσ.tendsto_atTop.eventually
      ((hSecondCap x k).mono (fun m hm => hm t ht))⟩)
  obtain ⟨η, hη, hComparison⟩ := actual_smooth_comparison_of_same_sequence
    X o u hu L ho h V hL hsol f p
    (fun m x t => openExtendedPotential_restrict X.manifold
      (sublevelOpens X.manifold u hu.1 o (L m)) (sublevelComponent_isConnected (ho m)) (V m) x t)
    (fun m x t => openExtendedPotential_restrict X.manifold
      (sublevelOpens X.manifold u hu.1 o (L m)) (sublevelComponent_isConnected (ho m))
      (flowLogDetRatio (approximatingMetric X.manifold X.metric.form u hu.1 o (L m) (ho m)) (h m)) x t)
    U (flowLogDetRatio X.metric.form hGlobal) σ hσ hPoint hPPoint
  exact ⟨hGlobal, U, flowLogDetRatio X.metric.form hGlobal,
    (fun x t => -flowLogDetRatio X.metric.form hGlobal x t), η, hη, hCore, hComparison⟩

end Yau.NodeProofs.F01Aux

namespace Yau.NodeProofs
open Yau Yau.Blueprint F01Aux

theorem F01_actual_proved : Yau.BlueprintContracts.F01_contract := by
  apply F01_contract_of_global_core_comparison
  intro n X o u hu hinitial
  exact actual_global_core_and_smooth_comparison X o u hu hinitial

end Yau.NodeProofs
