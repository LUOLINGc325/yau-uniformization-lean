import Yau.Proofs.P06HodgeRegularityScalarTranspose
import Yau.Proofs.P06HodgeRegularityWeakJets

/-! Lifting finite weak jets of (u,G) back to u. Each nonempty word
uses its final first-gradient slot; no two duplicated slots are identified. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux

variable {E ι α : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]

def regularityLiftJet (U : E → α → ℝ)
    (J : List ι → E → RegularityProlongIndex α ι → ℝ) (w : List ι) : E → α → ℝ :=
  match w.reverse with
  | [] => U
  | i::r => fun z c => J r.reverse z (c,some i)

@[simp] theorem regularityLiftJet_nil
    (U : E → α → ℝ) (J : List ι → E → RegularityProlongIndex α ι → ℝ) :
    regularityLiftJet U J [] = U := rfl

@[simp] theorem regularityLiftJet_append_singleton
    (U : E → α → ℝ) (J : List ι → E → RegularityProlongIndex α ι → ℝ)
    (w : List ι) (i : ι) :
    regularityLiftJet U J (w ++ [i]) = fun z c => J w z (c,some i) := by
  simp [regularityLiftJet, List.reverse_append]

theorem regularityLiftJet_isWeakJet
    (ν : Measure E) (O : Set E) (v : ι → E) (N : ℕ)
    (U : E → α → ℝ) (G : E → ι → α → ℝ)
    (J : List ι → E → RegularityProlongIndex α ι → ℝ)
    (hU : ∀ c, MemLp (fun z => U z c) 2 (ν.restrict O))
    (hG : ∀ i c, regularityWeakDeriv ν O (v i) (fun z => U z c) (fun z => G z i c))
    (hJ : regularityWeakJet ν O v N (regularityProlongWeakValue U G) J) :
    regularityWeakJet ν O v (N+1) U (regularityLiftJet U J) := by
  refine ⟨rfl, ?_, ?_⟩
  · intro w
    induction w using List.reverseRecOn with
    | nil => intro _ c; exact hU c
    | append_singleton w i _ =>
      intro hw c
      simp only [List.length_append, List.length_singleton] at hw
      simpa only [regularityLiftJet_append_singleton] using hJ.2.1 w (by omega) (c,some i)
  · intro w
    induction w using List.reverseRecOn with
    | nil =>
      intro _ i c
      have heq : (fun z => regularityLiftJet U J [i] z c) = fun z => G z i c := by
        rw [show [i] = [] ++ [i] from rfl, regularityLiftJet_append_singleton, hJ.1]
        rfl
      rw [heq]
      exact hG i c
    | append_singleton w j _ =>
      intro hw i c
      have hlen : w.length < N := by
        simp only [List.length_append, List.length_singleton] at hw
        omega
      have heq : i :: (w ++ [j]) = (i::w) ++ [j] := rfl
      rw [heq, regularityLiftJet_append_singleton, regularityLiftJet_append_singleton]
      exact hJ.2.2 w hlen i (c,some j)

end Yau.NodeProofs.P06Aux
