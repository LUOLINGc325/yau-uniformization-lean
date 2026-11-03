import Yau.Proofs.F05BootstrapExpPolynomial

/-! A finite derivative polynomial inherits the current joint order from
its displayed solution atoms. This is used inside the normal-order
bootstrap, without assuming smoothness of the candidate solution. -/

open Set
open scoped ContDiff
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic
variable {n : ℕ}

namespace F05GoodPolynomial

theorem contDiff_eval (P : F05GoodPolynomial n) {T : ℝ} {k : ℕ∞ω} {Q : Set (Point n)}
    {u : Point n → ℝ}
    (hAtoms : ∀ β ∈ P.atoms, ContDiffOn ℝ k (F05GoodWord T β u) Q) :
    ContDiffOn ℝ k (P.eval T u) Q := by
  revert hAtoms
  induction P with
  | constant c => intro hAtoms; exact contDiffOn_const
  | atom β => intro hAtoms; exact hAtoms β (by simp only [atoms,List.mem_singleton])
  | add P Q ihP ihQ =>
    intro hAtoms
    exact (ihP (fun β hβ => hAtoms β (List.mem_append_left _ hβ))).add
      (ihQ (fun β hβ => hAtoms β (List.mem_append_right _ hβ)))
  | mul P Q ihP ihQ =>
    intro hAtoms
    exact (ihP (fun β hβ => hAtoms β (List.mem_append_left _ hβ))).mul
      (ihQ (fun β hβ => hAtoms β (List.mem_append_right _ hβ)))

end F05GoodPolynomial

theorem F05_contDiffOn_list_sum {ι V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (xs : List ι) {k : ℕ∞ω} {Q : Set (Point n)} {f : ι → Point n → V}
    (hf : ∀ i ∈ xs, ContDiffOn ℝ k (f i) Q) :
    ContDiffOn ℝ k (fun z => (xs.map (fun i => f i z)).sum) Q := by
  induction xs with
  | nil => exact contDiffOn_const
  | cons i xs ih =>
    exact (hf i List.mem_cons_self).add (ih (fun j hj => hf j (List.mem_cons_of_mem _ hj)))

end Yau.Proofs.F05Aux
