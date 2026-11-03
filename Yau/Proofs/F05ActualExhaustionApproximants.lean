import Yau.Proofs.F05ExhaustionApproximants
import Yau.Proofs.HeatSmoothExhaustion

/-! The original manifold itself supplies the smooth nested exhaustion.
No domain family or existence premise remains in this approximant theorem. -/

open Set
open scoped Topology ContDiff
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.Blueprint Yau.F05Transport Yau.HeatConcreteBindings
variable {n : ℕ} {X : KahlerManifold n}

theorem F05_flow_actual_exhaustion_approximants
    (o : Pt X) (h : Flow X) (U P ρ : STF X) (hloc : LocalizedFlow X o h U P ρ)
    {T : ℝ} (hT : 0 < T) (v : STF X)
    (hVusc : UpperSemicontinuousOn (fun z : Pt X × ℝ => v z.1 z.2) (univ ×ˢ Icc 0 T))
    (hVLocal : ∀ K : Set (Pt X), IsCompact K → ∃ C : ℝ, ∀ x ∈ K, ∀ t ∈ Icc 0 T, |v x t| ≤ C)
    (hVRange : ∀ x t, t ∈ Icc 0 T → 0 ≤ v x t ∧ v x t ≤ ρ x t)
    (hVisc : NonlinearViscositySub h T v) :
    ∃ (O : ℕ → Set (Pt X)) (A : ℕ → AtlasData X.manifold)
      (χ : ∀ j, Fin (A j).count → Pt X → ℝ) (δ : ℕ → ℝ) (w : ℕ → STF X),
      SmoothExhaustion O ∧ ∀ j,
        GenuineAtlas (O j) (A j) ∧ F05Partition (O j) (A j) (χ j) ∧
        (closure (O j) ⊆ ⋃ i, lift (A j) i '' region ((A j).normal i) (1/8)) ∧
        (∀ i, IsCompact (lift (A j) i '' Metric.closedBall 0 3)) ∧ 0 < δ j ∧
        F05CompactDirichletSolution (O j) (A j) h
          (flowCornerBoundary X ρ (F05ExhaustionError j) (δ j) F05PaperCornerCutoff) T (w j) ∧
        (∀ x ∈ closure (O j), ∀ t ∈ Icc 0 T,
          0 ≤ w j x t ∧ w j x t ≤ ρ x t+2*F05ExhaustionError j) ∧
        (∀ s : ℝ, 0 < s → s < T → ∀ i,
          ContDiffOn ℝ ∞ (pull (A j) i (w j)) (F05D (A j) i ×ˢ Icc s T)) ∧
        ∀ x ∈ closure (O j), ∀ t ∈ Ico 0 T, v x t ≤ w j x t := by
  obtain ⟨O,hO⟩ := SmoothExhaustionAux.smoothExhaustion_exists X.manifold
  obtain ⟨A,χ,δ,w,hApprox⟩ := F05_flow_exhaustion_approximants O hO
    o h U P ρ hloc hT v hVusc hVLocal hVRange hVisc
  exact ⟨O,A,χ,δ,w,hO,hApprox⟩

end Yau.Proofs.F05Aux
