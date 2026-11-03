import Yau.Proofs.F05FlowHolder
import Yau.Proofs.F05PositiveTimeBootstrap
import Yau.Proofs.F05PositiveOpenCharts

/-! The native positive-time bootstrap discharges the qualitative
regularity condition in the original-flow uniform value Hölder theorem.
Its constants precede every candidate's finite Schauder exponent and norm. -/

open Set
open scoped ContDiff
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.Blueprint Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {X : KahlerManifold n}

theorem F05_flow_schauder_value_holder_uniform (hn : 0 < n)
    {O : Set (Pt X)} {A : AtlasData X.manifold} (hA : GenuineAtlas O A)
    {χ : Fin A.count → Pt X → ℝ} (hχ : F05Partition O A χ)
    (o : Pt X) (h : Flow X) (U P ρ : STF X) (hloc : LocalizedFlow X o h U P ρ)
    (p : STF X) {S a : ℝ} (hS : 0 < S) (hp : SmoothSpaceTime p (Icc 0 S)) :
    ∃ γ M : ℝ, 0 < γ ∧ γ < 1 ∧ 0 < M ∧ ∀ T : ℝ, 0 < T → T ≤ S →
      ∀ (β K : ℝ), 0 < β → β < 1 → ∀ w : STF X,
      ContinuousOn (fun z : Pt X × ℝ => w z.1 z.2) (closure O ×ˢ Icc 0 T) →
      (∀ i, SchauderBound β (F05Q A i T) (pull A i w) K) →
      (∀ x ∈ closure O, ∀ t ∈ Icc 0 T, 0 ≤ w x t ∧ w x t ≤ ρ x t+2*a) →
      (∀ x ∈ closure O, w x 0 = p x 0) →
      (∀ x ∈ frontier O, ∀ t ∈ Icc 0 T, w x t = p x t) →
      (∀ x ∈ closure O, ∀ t ∈ Icc 0 T,
        derivWithin (w x) (Icc 0 T) t = Real.exp (-w x t)*laplacian (h t) (fun y => w y t) x+
          (1-Real.exp (-w x t))*scalarCurvature (h t) x) →
      ∀ i,
        HolderBound γ (F05Q A i T) (pull A i (fun x t => Real.exp (w x t))) M ∧
        HolderBound γ (F05Q A i T) (pull A i w) M ∧
        HolderBound γ (F05Q A i T) (pull A i (fun x t => Real.exp (-w x t))) M := by
  obtain ⟨γ,M,hγ,hγ1,hM,hHolder⟩ := F05_flow_value_holder_uniform hn hA hχ o h U P ρ hloc p hS hp
  refine ⟨γ,M,hγ,hγ1,hM,?_⟩
  intro T hT hTS β K hβ hβ1 w hCont hW hBarrier hInitial hBoundary hEquation
  have hhT : MetricFamilySmooth h (Icc 0 T) := fun x j k =>
    (hloc.1.2.1 x j k).mono (fun z hz => ⟨hz.1,hz.2.1⟩)
  have hSub : Icc (0 : ℝ) T ⊆ Icc 0 S := fun t ht => ⟨ht.1,ht.2.trans hTS⟩
  have hpT : SmoothSpaceTime p (Icc 0 T) := fun x => (hp x).mono (prod_mono subset_rfl hSub)
  have hRT := F05_flow_scalar_smooth o h U P ρ hloc hT
  have hClosed := F05_positive_time_boundary_bootstrap hn hA h
    (fun x t => scalarCurvature (h t) x) p w hT hβ hβ1 hhT hRT hpT hCont hW hInitial hBoundary hEquation
  exact hHolder T hT hTS w (fun i => (hW i).1)
    (F05_positive_closed_to_open_charts hA w hClosed) hBarrier hInitial hBoundary hEquation

end Yau.Proofs.F05Aux
