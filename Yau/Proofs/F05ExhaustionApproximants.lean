import Yau.Proofs.F05FiniteHorizonApproximants
import Yau.Proofs.F05CompactAtlasPartition
import Yau.Proofs.F03PositiveDimension

/-! On any actual supplied smooth exhaustion, construct the paper's
genuine finite-horizon solutions for the original given viscosity
subsolution. Existence of the exhaustion is discharged separately by its
certified geometric producer when assembling the original contract. -/

open Set Filter
open scoped Topology ContDiff
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.Blueprint Yau.F05Transport Yau.HeatConcreteBindings
variable {n : ℕ} {X : KahlerManifold n}

def F05ExhaustionError (j : ℕ) : ℝ := 1/((j : ℝ)+1)

theorem F05_exhaustion_error_pos (j : ℕ) : 0 < F05ExhaustionError j := by
  unfold F05ExhaustionError
  positivity

theorem F05_exhaustion_error_le_one (j : ℕ) : F05ExhaustionError j ≤ 1 := by
  unfold F05ExhaustionError
  exact (div_le_one (by positivity)).2 (by linarith [Nat.cast_nonneg (α := ℝ) j])

theorem F05_exhaustion_error_tendsto : Tendsto F05ExhaustionError atTop (𝓝 0) := by
  change Tendsto (fun j : ℕ => 1/((j : ℝ)+1)) atTop (𝓝 0)
  exact tendsto_one_div_add_atTop_nhds_zero_nat

theorem F05_flow_exhaustion_approximants (O : ℕ → Set (Pt X)) (hO : SmoothExhaustion O)
    (o : Pt X) (h : Flow X) (U P ρ : STF X) (hloc : LocalizedFlow X o h U P ρ)
    {T : ℝ} (hT : 0 < T) (v : STF X)
    (hVusc : UpperSemicontinuousOn (fun z : Pt X × ℝ => v z.1 z.2) (univ ×ˢ Icc 0 T))
    (hVLocal : ∀ K : Set (Pt X), IsCompact K → ∃ C : ℝ, ∀ x ∈ K, ∀ t ∈ Icc 0 T, |v x t| ≤ C)
    (hVRange : ∀ x t, t ∈ Icc 0 T → 0 ≤ v x t ∧ v x t ≤ ρ x t)
    (hVisc : NonlinearViscositySub h T v) :
    ∃ (A : ℕ → AtlasData X.manifold)
      (χ : ∀ j, Fin (A j).count → Pt X → ℝ) (δ : ℕ → ℝ) (w : ℕ → STF X),
      ∀ j, GenuineAtlas (O j) (A j) ∧ F05Partition (O j) (A j) (χ j) ∧
        (closure (O j) ⊆ ⋃ i, lift (A j) i '' region ((A j).normal i) (1/8)) ∧
        (∀ i, IsCompact (lift (A j) i '' Metric.closedBall 0 3)) ∧ 0 < δ j ∧
        F05CompactDirichletSolution (O j) (A j) h
          (flowCornerBoundary X ρ (F05ExhaustionError j) (δ j) F05PaperCornerCutoff) T (w j) ∧
        (∀ x ∈ closure (O j), ∀ t ∈ Icc 0 T,
          0 ≤ w j x t ∧ w j x t ≤ ρ x t+2*F05ExhaustionError j) ∧
        (∀ s : ℝ, 0 < s → s < T → ∀ i,
          ContDiffOn ℝ ∞ (pull (A j) i (w j)) (F05D (A j) i ×ˢ Icc s T)) ∧
        ∀ x ∈ closure (O j), ∀ t ∈ Ico 0 T, v x t ≤ w j x t := by
  classical
  have hn := F03Aux.complexManifold_dimension_pos X.manifold
  choose A χ hA hχ hSmall hCompact using
    (fun j => F05_finite_compact_atlas_partition hn (O j) (hO.1 j))
  have hApprox (j : ℕ) := F05_flow_finite_horizon_approximant hn (hA j) (hχ j)
    o h U P ρ hloc hT le_rfl (F05_exhaustion_error_pos j) v hVusc hVLocal hVRange hVisc
  choose δ w hδ hSolution hBounds hBoundary hSmooth hComparison using hApprox
  exact ⟨A,χ,δ,w,fun j =>
    ⟨hA j,hχ j,hSmall j,hCompact j,hδ j,hSolution j,hBounds j,hSmooth j,hComparison j⟩⟩

end Yau.Proofs.F05Aux
