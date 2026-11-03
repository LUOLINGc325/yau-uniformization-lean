import Yau.Proofs.F01SpatialSchauderWords
import Yau.Proofs.F01PotentialSpatialLinearization
import Yau.Proofs.F01TransformedMatrixSpatialJets

/-! Spatial jets of the transformed potential matrix use the initial
potential Hessian and strictly earlier Schauder words of its first
native derivatives. The numerical matrix budget precedes all fields. -/
noncomputable section
open Set
open scoped ContDiff Matrix Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic
variable {n : ℕ}

theorem previous_schauder_matrix_jet_budget (k : ℕ) {Cs Cu : ℝ}
    (hCs : 0 ≤ Cs) (hCu : 0 ≤ Cu) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q : Set (Point n)) (O : Set (Space n)) (β : ℝ)
      (S : Point n → Matrix (Fin n) (Fin n) ℂ) (u : Point n → ℝ),
      IsOpen O → Q ⊆ O ×ˢ (Set.univ : Set ℝ) →
      HolderBound β Q S Cs →
      (∀ p ∈ Q, ContDiffOn ℝ ∞ (fun z => S (z, p.2)) O) →
      (∀ p ∈ Q, ContDiffOn ℝ ∞ (fun z => u (z, p.2)) O) →
      (∀ j : Fin (k + 1), HolderBound β Q
        (fun p => iteratedFDeriv ℝ j.val (fun z => S (z, p.2)) p.1) Cs) →
      HolderBound β Q (spatialDD u) Cu →
      (∀ (i : RIdx n) (ws : List (Space n)), NativeFrameWord ws → ws.length < k →
        SchauderBound β Q (spatialDerivativeWord ws (spatialDerivativeWord [realVec i] u)) Cu) →
      HolderBound β Q (chartPotentialMatrix S u) C ∧
      ∀ j : Fin (k + 1), HolderBound β Q
        (fun p => iteratedFDeriv ℝ j.val (fun z => chartPotentialMatrix S u (z, p.2)) p.1) C := by
  obtain ⟨C, hC, hBudget⟩ := transformed_matrix_spatial_jet_holder_budget (n := n) k hCs hCu
  refine ⟨C, hC, ?_⟩
  intro Q O β S u hO hQ hS hSs hus hSj hu hPrev
  apply hBudget Q O β S u hO hQ hS hSs hus hSj
  intro j m
  apply potential_word_hessian_from_previous hu hPrev
  · intro v hv
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp hv
    exact ⟨m i, hi.symm⟩
  · simpa only [List.length_ofFn] using Nat.le_of_lt_succ j.isLt

end Yau.NodeProofs.F01Aux
