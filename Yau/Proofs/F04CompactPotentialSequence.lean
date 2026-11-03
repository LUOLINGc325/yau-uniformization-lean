import Yau.Proofs.F04CompactSourcePotential
import Yau.Proofs.F04PotentialCutoffs

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold InnerProductSpace
noncomputable section
namespace Yau.F04Proof
open Yau.Blueprint

/-- The original controlled exhaustion constructs the genuine compact
 source-potential sequence. Source ordering is proved through the retained
 original finite weak records, so arbitrary choices of actual potentials
 still form a monotone sequence. Constants may depend on the source index. -/
theorem flow_compact_source_potential_sequence
    {n : ℕ} (hn : 0 < n) (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    (u : Pt X → ℝ) (hu : ControlledExhaustion X o u)
    {S T : ℝ} (hS : 0 < S) (hT : 0 < T) (hTS : T < S) :
    ∃ (qs : ℕ → Pt X → ℝ) (v : ℕ → STF X) (M : ℕ → ℝ),
      (∀ j, SmoothFn (qs j) ∧ HasCompactSupport (qs j) ∧ ∀ x, 0 ≤ qs j x ∧ qs j x ≤ 1) ∧
      (∀ K : Set (Pt X), IsCompact K → ∃ J : ℕ, ∀ j ≥ J, ∀ x ∈ K, qs j x = 1) ∧
      (∀ x t, t ∈ Icc 0 S → Monotone (fun j => v j x t)) ∧
      ∀ j, 0 ≤ M j ∧
        (∀ x t, t ∈ Icc 0 S → 0 ≤ v j x t ∧ v j x t ≤ ρ x t ∧ v j x t ≤ M j*t) ∧
        (∀ x, v j x 0 = 0) ∧ SmoothSpaceTime (v j) (Ioo 0 S) ∧
        (∀ x t, t ∈ Ioo 0 S → heatOp h (Icc 0 S) (v j) x t = qs j x * source X h x t) ∧
        SmoothSpaceTime (v j) (Icc 0 T) ∧
        (∀ x t, t ∈ Icc 0 T → heatOp h (Icc 0 T) (v j) x t = qs j x * source X h x t) := by
  classical
  obtain ⟨qs,hqs,hqMono,hCut⟩ := controlled_exhaustion_potential_cutoffs X o u hu
  have hExists (j : ℕ) := flow_compact_source_classical_potential hn X o h U P ρ hloc μ hμ u hu
    hS hT hTS (qs j) (hqs j).1 (hqs j).2.2 (hqs j).2.1
  choose M hM v z hData hTend hBound h0 hPos hEq hClosed hClosedEq using hExists
  refine ⟨qs,z,M,hqs,hCut,?_,?_⟩
  · intro x t ht i j hij
    exact finite_potential_limits_source_le X o h U P ρ hloc μ hμ u hu hS
      (fun y => hqMono y hij) (v i) (v j) (z i) (z j) (hData i) (hData j) (hTend i) (hTend j) x t ht
  · intro j
    exact ⟨hM j,hBound j,h0 j,hPos j,hEq j,hClosed j,hClosedEq j⟩

end Yau.F04Proof
