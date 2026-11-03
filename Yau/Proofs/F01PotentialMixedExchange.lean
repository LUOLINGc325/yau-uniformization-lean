import Yau.Proofs.F01LeviClosedJets
import Yau.Proofs.F01MixedWirtingerLinearity

/-! An actual scalar-potential difference of two Hermitian matrix fields
has the precise diagonal second-derivative exchange used by the flow. -/
noncomputable section
open Set Filter
open scoped Matrix ContDiff Topology
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs
variable {n : ℕ}

theorem potential_difference_wirt_closed
    (H K : ComplexVector n → Matrix (Fin n) (Fin n) ℂ)
    (f : ComplexVector n → ℝ) {S : Set (ComplexVector n)} (hS : IsOpen S)
    (hf : ContDiffOn ℝ ∞ f S)
    (hpot : ∀ w ∈ S, K w - H w = leviC f w)
    {z : ComplexVector n} (hz : z ∈ S) (i j k : Fin n) :
    wirt (fun w => (K w - H w) i j) z (stdVec k) =
      wirt (fun w => (K w - H w) i k) z (stdVec j) := by
  have hgerm (p q : Fin n) : (fun w => (K w - H w) p q) =ᶠ[𝓝 z]
      (fun w => leviC f w p q) := by
    filter_upwards [hS.mem_nhds hz] with w hw
    exact congrFun (congrFun (hpot w hw) p) q
  rw [wirt_eq_of_eventuallyEq (hgerm i j), wirt_eq_of_eventuallyEq (hgerm i k)]
  exact leviC_wirt_closed f hS hf hz i j k

theorem potential_difference_diagonal_mixed_exchange
    (H K : ComplexVector n → Matrix (Fin n) (Fin n) ℂ)
    (hH : ∀ w, (H w).IsHermitian) (hK : ∀ w, (K w).IsHermitian)
    (f : ComplexVector n → ℝ) {S : Set (ComplexVector n)} (hS : IsOpen S)
    (hHs : ∀ p q, ContDiffOn ℝ ∞ (fun w => H w p q) S)
    (hKs : ∀ p q, ContDiffOn ℝ ∞ (fun w => K w p q) S)
    (hf : ContDiffOn ℝ ∞ f S)
    (hpot : ∀ w ∈ S, K w - H w = leviC f w)
    {z : ComplexVector n} (hz : z ∈ S) (i a : Fin n) :
    wirt (fun w => wirtBar (fun y => K y i i) w (stdVec a)) z (stdVec a) -
        wirt (fun w => wirtBar (fun y => K y a a) w (stdVec i)) z (stdVec i) =
      wirt (fun w => wirtBar (fun y => H y i i) w (stdVec a)) z (stdVec a) -
        wirt (fun w => wirtBar (fun y => H y a a) w (stdVec i)) z (stdVec i) := by
  have hd : ∀ p q, ContDiffAt ℝ 2 (fun w => (K w - H w) p q) z := by
    intro p q
    exact (((hKs p q).sub (hHs p q)).contDiffAt (hS.mem_nhds hz)).of_le (by simp)
  have hex := kahler_diagonal_mixed_exchange (fun w => K w - H w)
    (fun w => (hK w).sub (hH w)) hS hz hd
    (fun w hw p q l => potential_difference_wirt_closed H K f hS hf hpot hw p q l) i a
  change wirt (fun w => wirtBar (fun y => K y i i - H y i i) w (stdVec a)) z (stdVec a) =
    wirt (fun w => wirtBar (fun y => K y a a - H y a a) w (stdVec i)) z (stdVec i) at hex
  rw [mixed_wirt_sub _ _ hS (hKs i i) (hHs i i) hz,
    mixed_wirt_sub _ _ hS (hKs a a) (hHs a a) hz] at hex
  linear_combination hex

end Yau.NodeProofs.F01Aux
