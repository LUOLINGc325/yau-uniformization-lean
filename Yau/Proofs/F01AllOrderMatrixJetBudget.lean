import Yau.Proofs.F01PreviousMatrixJetBudget
import Yau.Proofs.F01SchauderClosedRestriction
import Yau.Proofs.F01ZeroSpatialJetHolder

/-! All spatial operator-tensor jets of background plus native Levi
are controlled by the actual all-order Schauder words. Each numerical
budget is chosen before the fields, domain and Holder exponent. -/
noncomputable section
open Set
open scoped ContDiff Matrix Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic
variable {n : ℕ}

theorem all_order_matrix_jet_budgets (Cs Cu : ℕ → ℝ)
    (hCs : ∀ j, 0 < Cs j) (hCu : ∀ j, 0 < Cu j) {Ci : ℝ} (hCi : 0 ≤ Ci) :
    ∀ k : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ (Q : Set (Point n)) (O : Set (Space n)) (β : ℝ)
      (S : Point n → Matrix (Fin n) (Fin n) ℂ) (u : Point n → ℝ),
      IsOpen O → Q ⊆ O ×ˢ (Set.univ : Set ℝ) →
      (∀ p ∈ Q, ContDiffOn ℝ ∞ (fun z => S (z, p.2)) O) →
      (∀ p ∈ Q, ContDiffOn ℝ ∞ (fun z => u (z, p.2)) O) →
      (∀ j : ℕ, HolderBound β Q (fun p => iteratedFDeriv ℝ j (fun z => S (z, p.2)) p.1) (Cs j)) →
      HolderBound β Q (spatialDD u) Ci →
      (∀ (i : RIdx n) (ws : List (Space n)), NativeFrameWord ws →
        SchauderBound β Q (spatialDerivativeWord ws (spatialDerivativeWord [realVec i] u)) (Cu ws.length)) →
      HolderBound β Q
        (fun p => iteratedFDeriv ℝ k (fun z => chartPotentialMatrix S u (z, p.2)) p.1) C := by
  classical
  intro k
  let Bs : ℝ := 1 + ∑ j : Fin (k + 1), Cs j.val
  let Bu : ℝ := 1 + Ci + ∑ j : Fin k, Cu j.val
  have hSs : 0 ≤ ∑ j : Fin (k + 1), Cs j.val := Finset.sum_nonneg (fun j _ => (hCs j).le)
  have hSu : 0 ≤ ∑ j : Fin k, Cu j.val := Finset.sum_nonneg (fun j _ => (hCu j).le)
  have hBs : 0 ≤ Bs := by dsimp only [Bs]; linarith
  have hBu : 0 ≤ Bu := by dsimp only [Bu]; linarith
  have hCiBu : Ci ≤ Bu := by dsimp only [Bu]; linarith
  have hsBudget (j : Fin (k + 1)) : Cs j.val ≤ Bs := by
    have hh := Finset.single_le_sum (s := (Finset.univ : Finset (Fin (k + 1))))
      (fun i _ => (hCs i.val).le) (Finset.mem_univ j)
    dsimp only [Bs]
    linarith
  have huBudget (j : Fin k) : Cu j.val ≤ Bu := by
    have hh := Finset.single_le_sum (s := (Finset.univ : Finset (Fin k)))
      (fun i _ => (hCu i.val).le) (Finset.mem_univ j)
    dsimp only [Bu]
    linarith
  obtain ⟨C, hC, hMatrix⟩ := previous_schauder_matrix_jet_budget (n := n) k hBs hBu
  refine ⟨C, hC, ?_⟩
  intro Q O β S u hO hQ hSs hus hSj hInitial hWords
  have hSField := holderBound_from_zero_spatial_jet (n := n)
    (F := Matrix (Fin n) (Fin n) ℂ) (f := S) (hSj 0)
  have hBase : HolderBound β Q (spatialDD u) Bu := holderBound_mono_const hInitial hCiBu
  have hPrevious (i : RIdx n) (ws : List (Space n)) (hws : NativeFrameWord ws) (hlen : ws.length < k) :
      SchauderBound β Q (spatialDerivativeWord ws (spatialDerivativeWord [realVec i] u)) Bu :=
    schauderBound_mono_const (hWords i ws hws) (huBudget ⟨ws.length, hlen⟩)
  have hh := hMatrix Q O β S u hO hQ
    (holderBound_mono_const hSField (hsBudget ⟨0, by omega⟩)) hSs hus
    (fun j => holderBound_mono_const (hSj j) (hsBudget j)) hBase hPrevious
  exact hh.2 ⟨k, by omega⟩

end Yau.NodeProofs.F01Aux
