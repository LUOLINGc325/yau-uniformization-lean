import Yau.Proofs.P06HodgeRegularityLocalH1
import Yau.Proofs.P06HodgeRegularityWeakProlongation
import Yau.Proofs.P06HodgeRegularityJetLift

/-! N genuine forward graph edges give N local weak jets. The induction
packs one layer at a time and uses only independent first weak gradients.
Its compact buffers depend on the prescribed regions alone. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux

variable {E : Type*} {ι α : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [Fintype ι] [Fintype α] [DecidableEq ι] [DecidableEq α]
    (ν : Measure E) [ν.IsAddHaarMeasure] [ν.IsNegInvariant] [SigmaFinite ν]

theorem regularityForwardChain_weakJet (N : ℕ)
    (v : ι → E) (q : ι → ι → E → ℝ)
    (e1 : α → α → ι → E → ℝ) (e0 : α → α → E → ℝ)
    (hq : ∀ i j, ContDiff ℝ ∞ (q i j)) (hcq : ∀ i j, HasCompactSupport (q i j))
    (he1 : ∀ r c i, ContDiff ℝ ∞ (e1 r c i)) (hce1 : ∀ r c i, HasCompactSupport (e1 r c i))
    (he0 : ∀ r c, ContDiff ℝ ∞ (e0 r c)) (hce0 : ∀ r c, HasCompactSupport (e0 r c))
    {O V : Set E} (hO : IsOpen O) (hV : IsOpen V)
    (hcV : IsCompact (closure V)) (hVO : closure V ⊆ O)
    (ell : ℝ) (hell : 0 < ell)
    (hcoercive : ∀ z ∈ O, ∀ ξ : ι → ℝ,
      ell * ∑ i, (ξ i)^2 ≤ ∑ i, ∑ j, q i j z * ξ j * ξ i)
    (U : ℕ → E → α → ℝ)
    (hU : ∀ j ≤ N, ∀ c, MemLp (fun z => U j z c) 2 (ν.restrict O))
    (hedge : ∀ j < N, regularityForwardWeak ν O v q e1 e0 (U j) (U (j+1))) :
    ∃ J : List ι → E → α → ℝ, regularityWeakJet ν V v N (U 0) J := by
  induction N generalizing α O V with
  | zero =>
    refine ⟨fun _ => U 0, rfl, ?_, ?_⟩
    · intro w hw c
      exact (hU 0 (by omega) c).mono_measure
        (Measure.restrict_mono (subset_closure.trans hVO) le_rfl)
    · intro w hw
      omega
  | succ N ih =>
    obtain ⟨W,hW,hVW,hWO,hcW⟩ := exists_open_between_and_isCompact_closure hcV hO hVO
    have hWsub : W ⊆ O := subset_closure.trans hWO
    have hVsub : V ⊆ W := subset_closure.trans hVW
    have hgrad (j : Fin (N+1)) : ∃ G : E → ι → α → ℝ,
        (∀ i c, MemLp (fun z => G z i c) 2 (ν.restrict W)) ∧
        ∀ i c, regularityWeakDeriv ν W (v i) (fun z => U j z c) (fun z => G z i c) :=
      regularityForwardWeak_local_h1 ν v q e1 e0 hq hcq he1 hce1 he0 hce0
        hO hW hcW hWO ell hell hcoercive (U j) (U (j+1))
        (hU j (by omega)) (hU (j+1) (by omega)) (hedge j (by omega))
    choose G hGL hGD using hgrad
    let Up : ℕ → E → RegularityProlongIndex α ι → ℝ := fun j =>
      if hj : j ≤ N then regularityProlongWeakValue (U j) (G ⟨j,by omega⟩) else 0
    have hUp (j : ℕ) (hj : j ≤ N) (c : RegularityProlongIndex α ι) :
        MemLp (fun z => Up j z c) 2 (ν.restrict W) := by
      dsimp only [Up]
      rw [dif_pos hj]
      exact regularityProlongWeakValue_memLp ν (U j) _
        (fun c => (hU j (by omega) c).mono_measure (Measure.restrict_mono hWsub le_rfl))
        (hGL ⟨j,by omega⟩) c
    have hEdge (j : ℕ) (hj : j < N) :
        regularityForwardWeak ν W v q (regularityProlongE1 v q e1) (regularityProlongE0 v e1 e0)
          (Up j) (Up (j+1)) := by
      have hWedge := regularityForwardWeak_mono ν v q e1 e0 hq he1 he0
        (hedge j (by omega)) hWsub
      have hp := regularityForwardWeak_prolong ν v q e1 e0 hq he1 he0
        (U j) (U (j+1)) (G ⟨j,by omega⟩) (G ⟨j+1,by omega⟩)
        (fun c => (hU j (by omega) c).mono_measure (Measure.restrict_mono hWsub le_rfl))
        (hGL ⟨j,by omega⟩) (hGD ⟨j,by omega⟩) (hGD ⟨j+1,by omega⟩) hWedge
      simpa only [Up, dif_pos (show j ≤ N by omega), dif_pos (show j+1 ≤ N by omega)] using hp
    have hp1 := regularityProlongE1_regular v q e1 hq hcq he1 hce1
    have hp0 := regularityProlongE0_regular v e1 e0 he1 hce1 he0 hce0
    obtain ⟨J,hJ⟩ := ih (α := RegularityProlongIndex α ι)
      (regularityProlongE1 v q e1) (regularityProlongE0 v e1 e0)
      (fun r c i => (hp1 r c i).1) (fun r c i => (hp1 r c i).2)
      (fun r c => (hp0 r c).1) (fun r c => (hp0 r c).2)
      hW hV hcV hVW (fun z hz => hcoercive z (hWsub hz)) Up hUp hEdge
    have hJ' : regularityWeakJet ν V v N
        (regularityProlongWeakValue (U 0) (G ⟨0,by omega⟩)) J := by
      simpa only [Up,dif_pos (Nat.zero_le N)] using hJ
    refine ⟨regularityLiftJet (U 0) J,?_⟩
    exact regularityLiftJet_isWeakJet ν V v N (U 0) (G ⟨0,by omega⟩) J
      (fun c => (hU 0 (by omega) c).mono_measure
        (Measure.restrict_mono (subset_closure.trans hVO) le_rfl))
      (fun i c => regularityWeakDeriv_mono ν (hGD ⟨0,by omega⟩ i c) hVsub) hJ'

end Yau.NodeProofs.P06Aux
