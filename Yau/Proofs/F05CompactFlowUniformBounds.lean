import Yau.Proofs.F05CompactDirichletSolution
import Yau.Proofs.F05FlowClassicalBarriers
import Yau.Proofs.F05FlowFullSchauder

/-! Every actual compact solution inherits the supplied flow barriers.
The resulting positive-time complete chart estimate is fixed before all
admissible endpoints, candidates and their original finite norms. -/

open Set
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.Blueprint Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {X : KahlerManifold n}

theorem F05_compact_flow_barriers {O : Set (Pt X)} {A : AtlasData X.manifold}
    (hA : GenuineAtlas O A) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ) (p w : STF X) {S T a : ℝ}
    (hT : 0 < T) (hTS : T ≤ S) (ha : 0 ≤ a)
    (hp0 : ∀ x ∈ closure O, p x 0 = a)
    (hpB : ∀ x ∈ frontier O, ∀ t ∈ Icc 0 S, 0 ≤ p x t ∧ p x t ≤ ρ x t+2*a)
    (hw : F05CompactDirichletSolution O A h p T w) :
    ∀ x ∈ closure O, ∀ t ∈ Icc 0 T, 0 ≤ w x t ∧ w x t ≤ ρ x t+2*a := by
  obtain ⟨β,K,hβ,hβ1,hK,hSch,hCont,h0,hBoundary,hEq⟩ := hw
  have hInitial (x : Pt X) (hx : x ∈ closure O) : w x 0 = a :=
    (h0 x hx).trans (hp0 x hx)
  have hLateral (x : Pt X) (hx : x ∈ frontier O) (t : ℝ) (ht : t ∈ Icc 0 T) :
      0 ≤ w x t ∧ w x t ≤ ρ x t+2*a := by
    rw [hBoundary x hx t ht]
    exact hpB x hx t ⟨ht.1,ht.2.trans hTS⟩
  exact F05_flow_classical_barriers hA o h U P ρ hloc hT ha w hCont
    (fun i => (hSch i).1) hInitial hLateral
    (fun x hx t ht => hEq x (subset_closure hx) t ⟨ht.1.le,ht.2⟩)

theorem F05_compact_flow_uniform_positive_schauder (hn : 0 < n)
    {O : Set (Pt X)} {A : AtlasData X.manifold} (hA : GenuineAtlas O A)
    {χ : Fin A.count → Pt X → ℝ} (hχ : F05Partition O A χ)
    (o : Pt X) (h : Flow X) (U P ρ : STF X) (hloc : LocalizedFlow X o h U P ρ)
    (p : STF X) {S a s : ℝ} (hS : 0 < S) (hp : SmoothSpaceTime p (Icc 0 S))
    (hs : 0 < s) (hsS : s < S) (ha : 0 ≤ a)
    (hp0 : ∀ x ∈ closure O, p x 0 = a)
    (hpB : ∀ x ∈ frontier O, ∀ t ∈ Icc 0 S, 0 ≤ p x t ∧ p x t ≤ ρ x t+2*a) :
    ∃ γ C : ℝ, 0 < γ ∧ γ < 1 ∧ 0 < C ∧
      ∀ T : ℝ, s < T → T ≤ S → ∀ w : STF X,
      F05CompactDirichletSolution O A h p T w →
      ∀ i, F05RelSchauder γ (F05D A i) (Icc s T) (pull A i w) C := by
  obtain ⟨γ,C,hγ,hγ1,hC,hEstimate⟩ :=
    F05_flow_full_positive_schauder_uniform (a := a) hn hA hχ o h U P ρ hloc p hS hp hs hsS
  refine ⟨γ,C,hγ,hγ1,hC,?_⟩
  intro T hsT hTS w hw
  have hBarrier := F05_compact_flow_barriers hA o h U P ρ hloc p w
    (hs.trans hsT) hTS ha hp0 hpB hw
  obtain ⟨β,K,hβ,hβ1,hK,hSch,hCont,h0,hBoundary,hEq⟩ := hw
  exact hEstimate T hsT hTS β K hβ hβ1 w hCont hSch hBarrier h0 hBoundary hEq

end Yau.Proofs.F05Aux
