import Yau.Proofs.F01ScalarSymbolSpatialJets
import Yau.Proofs.F01FiniteBudgets

/-! One coefficient budget covers every spatial order through a fixed
order. It is chosen before the positive matrix field and all chart data. -/
noncomputable section
open Set
open scoped ContDiff Matrix ComplexOrder Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic Yau.LeafProofs.L17Aux
variable {n : ℕ}

theorem scalarSymbol_uniform_spatial_jet_budget {ell C : ℝ}
    (hell : 0 < ell) (hC : 0 ≤ C) (r : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ (Q : Set (Point n)) (O : Set (Space n)) (β : ℝ)
      (H : Point n → Matrix (Fin n) (Fin n) ℂ),
      IsOpen O → Q ⊆ O ×ˢ (Set.univ : Set ℝ) → HolderBound β Q H C →
      (∀ p ∈ Q, (H p - (ell : ℂ) • 1).PosSemidef) →
      (∀ p ∈ Q, ContDiffOn ℝ ∞ (fun z => H (z, p.2)) O) →
      (∀ j : ℕ, j ≤ r → HolderBound β Q
        (fun p => iteratedFDeriv ℝ j (fun z => H (z, p.2)) p.1) C) →
      ∀ j : ℕ, j ≤ r → HolderBound β Q
        (fun p => iteratedFDeriv ℝ j (fun z => scalarSymbol (H (z, p.2))) p.1) B := by
  classical
  have each := fun j : Fin (r + 1) =>
    scalarSymbol_spatial_jet_holder_budget (n := n) hell hC j.val
  choose A hA hEst using each
  obtain ⟨B, hB, _hAB, hAB0⟩ := exists_finite_uniform_budgets
    (Finset.univ : Finset (Fin (r + 1))) (fun j _ => A j) A
  refine ⟨B 0, hB 0, ?_⟩
  intro Q O β H hO hQ hH hlo hs hj j hjr
  let i : Fin (r + 1) := ⟨j, by omega⟩
  apply holderBound_mono_const
    (hEst i Q O β H hO hQ hH hlo hs (fun l => hj l.val (by have hh := l.isLt; dsimp only [i] at hh; omega)))
  exact hAB0 i (Finset.mem_univ _)

end Yau.NodeProofs.F01Aux
