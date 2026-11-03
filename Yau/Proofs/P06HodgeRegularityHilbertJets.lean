import Yau.Proofs.P06HodgeRegularityHodgeJets
import Yau.Proofs.P06StrongPathRegularity

/-! Genuine finite Hilbert closed-graph chains give compact chart weak
jets of any chosen actual representative of their first entry. -/
noncomputable section
open MeasureTheory Filter Module
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux
open Yau Yau.LeafProofs Yau.LeafProofs.L03

variable {n k : ℕ} {M : ComplexManifold n}

theorem hodgeHilbertGraph_chain_cutoff_weakJet {α : Type} [Fintype α] [DecidableEq α]
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (N : ℕ) (u : ℕ → L2FormHilbert g μ k)
    (hgraph : ∀ j < N, (u j,u (j+1)) ∈ (hodgeCoreOperator g μ hμ k).closure.graph)
    (A : RealForm M k) (hA : L2RealForm g.form μ A) (hAu : realizeActualForm g μ A hA = u 0)
    (x : M.Carrier) (b : Basis α ℝ (HodgeJets.Fiber n k))
    (χ : ComplexVector n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hχO : tsupport χ ⊆ chartTarget x) :
    ∃ J : List (RIdx n) → ComplexVector n → α → ℝ,
      regularityWeakJet (lebesgueC n) Set.univ (realModelBasis n) N
        (fun z c => χ z * hodgeRegularityCoord b A x z c) J ∧
      ∀ w c, tsupport (fun z => J w z c) ⊆ tsupport χ := by
  classical
  choose B hB hBr using fun j => l2FormHilbert_exists_section g μ (u j)
  let As (j : ℕ) : RealForm M k := if j = 0 then A else B j
  have hAs (j : ℕ) : L2RealForm g.form μ (As j) := by
    by_cases hj : j = 0
    · simpa only [As,if_pos hj] using hA
    · simpa only [As,if_neg hj] using hB j
  have hr (j : ℕ) : realizeActualForm g μ (As j) (hAs j) = u j := by
    by_cases hj : j = 0
    · subst j
      simpa only [As,ite_true] using hAu
    · simpa only [As,if_neg hj,realizeActualForm] using hBr j
  obtain ⟨J,hJ⟩ := hodgeClosureGraph_chain_cutoff_weakJet g μ hμ N As
    (fun j _ => hAs j) (fun j hj => by simpa only [hr] using hgraph j hj) x b χ hχ hcχ hχO
  refine ⟨J,?_⟩
  simpa only [As,ite_true] using hJ

theorem hodgeStrongPath_cutoff_weakJet {α : Type} [Fintype α] [DecidableEq α]
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (h : ℝ → L2FormHilbert g μ k)
    (hheat : ∀ t, 0 < t → ∃ w, HasDerivAt h w t ∧
      (h t,(-2 : ℝ) • w) ∈ (hodgeCoreOperator g μ hμ k).closure.graph)
    {t : ℝ} (ht : 0 < t) (N : ℕ)
    (A : RealForm M k) (hA : L2RealForm g.form μ A) (hAt : realizeActualForm g μ A hA = h t)
    (x : M.Carrier) (b : Basis α ℝ (HodgeJets.Fiber n k))
    (χ : ComplexVector n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hχO : tsupport χ ⊆ chartTarget x) :
    ∃ J : List (RIdx n) → ComplexVector n → α → ℝ,
      regularityWeakJet (lebesgueC n) Set.univ (realModelBasis n) N
        (fun z c => χ z * hodgeRegularityCoord b A x z c) J ∧
      ∀ w c, tsupport (fun z => J w z c) ⊆ tsupport χ := by
  obtain ⟨u,hu,hgraph,_⟩ := hodgeStrongPath_bounded_graph_chain g μ hμ k h hheat ht N
  exact hodgeHilbertGraph_chain_cutoff_weakJet g μ hμ N u hgraph A hA (hAt.trans hu.symm) x b χ hχ hcχ hχO

end Yau.NodeProofs.P06Aux
