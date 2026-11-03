import Yau.Proofs.F05FlowPositiveSchauder
import Yau.Proofs.F05FullChartSchauder

/-! The uniform continuation norm reaches every full receiving chart.
No artificial rim datum or candidate derivative bound enters the estimate. -/

open Set
open scoped ContDiff
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.Blueprint Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {X : KahlerManifold n}

theorem F05_flow_full_positive_schauder_uniform (hn : 0 < n)
    {O : Set (Pt X)} {A : AtlasData X.manifold} (hA : GenuineAtlas O A)
    {χ : Fin A.count → Pt X → ℝ} (hχ : F05Partition O A χ)
    (o : Pt X) (h : Flow X) (U P ρ : STF X) (hloc : LocalizedFlow X o h U P ρ)
    (p : STF X) {S a s : ℝ} (hS : 0 < S) (hp : SmoothSpaceTime p (Icc 0 S))
    (hs : 0 < s) (hsS : s < S) :
    ∃ γ C : ℝ, 0 < γ ∧ γ < 1 ∧ 0 < C ∧ ∀ T : ℝ, s < T → T ≤ S →
      ∀ (β K : ℝ), 0 < β → β < 1 → ∀ w : STF X,
      ContinuousOn (fun z : Pt X × ℝ => w z.1 z.2) (closure O ×ˢ Icc 0 T) →
      (∀ i, SchauderBound β (F05Q A i T) (pull A i w) K) →
      (∀ x ∈ closure O, ∀ t ∈ Icc 0 T, 0 ≤ w x t ∧ w x t ≤ ρ x t+2*a) →
      (∀ x ∈ closure O, w x 0 = p x 0) →
      (∀ x ∈ frontier O, ∀ t ∈ Icc 0 T, w x t = p x t) →
      (∀ x ∈ closure O, ∀ t ∈ Icc 0 T,
        derivWithin (w x) (Icc 0 T) t = Real.exp (-w x t)*laplacian (h t) (fun y => w y t) x+
          (1-Real.exp (-w x t))*scalarCurvature (h t) x) →
      ∀ i, F05RelSchauder γ (F05D A i) (Icc s T) (pull A i w) C := by
  obtain ⟨γ,C0,hγ,hγ1,hC0,hInner⟩ := F05_flow_positive_schauder_uniform hn hA hχ
    o h U P ρ hloc p hS hp hs hsS
  obtain ⟨CG,hCG,hFull⟩ := F05_inner_schauder_to_full hA hγ hγ1 hs.le S
  refine ⟨γ,CG*C0,hγ,hγ1,mul_pos hCG hC0,?_⟩
  intro T hsT hTS β K hβ hβ1 w hCont hW hBarrier hInitial hBoundary hEquation
  exact hFull T C0 w hsT hTS hC0.le (fun i => (hW i).1)
    (hInner T hsT hTS β K hβ hβ1 w hCont hW hBarrier hInitial hBoundary hEquation)

end Yau.Proofs.F05Aux
