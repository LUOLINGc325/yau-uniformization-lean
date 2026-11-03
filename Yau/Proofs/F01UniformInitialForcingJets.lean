import Yau.Proofs.F01InitialForcingScalarJets
import Yau.Proofs.F01FiniteBudgets

/-! One forcing budget covers every spatial order through a fixed
order and every unit direction, before all realized matrix fields. -/
noncomputable section
open Set
open scoped ContDiff Matrix ComplexOrder Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic
variable {n : ℕ}

theorem initial_forcing_uniform_spatial_jet_budget {ell C : ℝ}
    (hell : 0 < ell) (hC : 0 ≤ C) (r : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ (Q : Set (Point n)) (O : Set (Space n)) (β : ℝ)
      (H S : Point n → Matrix (Fin n) (Fin n) ℂ) (b : Point n → ℝ),
      IsOpen O → Q ⊆ O ×ˢ (Set.univ : Set ℝ) →
      (∀ p ∈ Q, (H p - (ell : ℂ) • 1).PosSemidef) →
      (∀ p ∈ Q, ∀ z ∈ O, (H (z, p.2)).PosDef) →
      (∀ p ∈ Q, ContDiffOn ℝ ∞ (fun z => H (z, p.2)) O) →
      (∀ p ∈ Q, ContDiffOn ℝ ∞ (fun z => S (z, p.2)) O) →
      (∀ p ∈ Q, ContDiffOn ℝ ∞ (fun z => b (z, p.2)) O) →
      (∀ j : ℕ, j ≤ r → HolderBound β Q
        (fun p => iteratedFDeriv ℝ j (fun z => H (z, p.2)) p.1) C) →
      (∀ j : ℕ, j ≤ r + 1 → HolderBound β Q
        (fun p => iteratedFDeriv ℝ j (fun z => S (z, p.2)) p.1) C) →
      (∀ j : ℕ, j ≤ r + 1 → HolderBound β Q
        (fun p => iteratedFDeriv ℝ j (fun z => b (z, p.2)) p.1) C) →
      ∀ v : Space n, ‖v‖ ≤ 1 → ∀ j : ℕ, j ≤ r → HolderBound β Q (fun p => iteratedFDeriv ℝ j
        (fun z => traceWith (H (z, p.2)) (fderiv ℝ (fun y => S (y, p.2)) z v) +
          fderiv ℝ (fun y => b (y, p.2)) z v) p.1) B := by
  classical
  have each := fun i : Fin (r + 1) =>
    initial_forcing_spatial_scalar_jet_budget (n := n) hell hC i.val
  choose A hA hEst using each
  obtain ⟨B, hB, _hAB, hAB0⟩ := exists_finite_uniform_budgets
    (Finset.univ : Finset (Fin (r + 1))) (fun i _ => A i) A
  refine ⟨B 0, hB 0, ?_⟩
  intro Q O β H S b hO hQ hlo hpos hHs hSs hbs hHj hSj hbj v hv j hjr
  let i : Fin (r + 1) := ⟨j, by omega⟩
  have hBound := hEst i Q O β H S b hO hQ hlo hpos hHs hSs hbs
    (fun l hl => hHj l (by dsimp only [i] at hl; omega))
    (fun l hl => hSj l (by dsimp only [i] at hl; omega))
    (fun l hl => hbj l (by dsimp only [i] at hl; omega)) v hv
  exact holderBound_mono_const hBound (hAB0 i (Finset.mem_univ _))

end Yau.NodeProofs.F01Aux
