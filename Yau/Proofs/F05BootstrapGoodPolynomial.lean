import Yau.Proofs.F05BootstrapGoodAlgebra

/-! Finite product-rule polynomials in actual solution good words. The
symbolic derivative is certified from only its finite displayed atoms;
there is no all-orders regularity assumption on the nonlinear coefficient. -/

open Set
noncomputable section
set_option maxHeartbeats 1800000
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux
variable {n : ℕ}

inductive F05GoodPolynomial (n : ℕ) where
  | constant : ℝ → F05GoodPolynomial n
  | atom : List (Option (RIdx n)) → F05GoodPolynomial n
  | add : F05GoodPolynomial n → F05GoodPolynomial n → F05GoodPolynomial n
  | mul : F05GoodPolynomial n → F05GoodPolynomial n → F05GoodPolynomial n

namespace F05GoodPolynomial

def eval : F05GoodPolynomial n → ℝ → (Point n → ℝ) → Point n → ℝ
  | .constant c,_,_,_ => c
  | .atom β,T,u,z => F05GoodWord T β u z
  | .add P Q,T,u,z => P.eval T u z+Q.eval T u z
  | .mul P Q,T,u,z => P.eval T u z*Q.eval T u z

def atoms : F05GoodPolynomial n → List (List (Option (RIdx n)))
  | .constant _ => []
  | .atom β => [β]
  | .add P Q => P.atoms++Q.atoms
  | .mul P Q => P.atoms++Q.atoms

def derivative (d : Option (RIdx n)) : F05GoodPolynomial n → F05GoodPolynomial n
  | .constant _ => .constant 0
  | .atom β => .atom (d::β)
  | .add P Q => .add (P.derivative d) (Q.derivative d)
  | .mul P Q => .add (.mul (P.derivative d) Q) (.mul P (Q.derivative d))

def budget (B : ℝ) : F05GoodPolynomial n → ℝ
  | .constant c => |c|
  | .atom _ => B
  | .add P Q => P.budget B+Q.budget B
  | .mul P Q => 2*P.budget B*Q.budget B

theorem good_diff (P : F05GoodPolynomial n) {T : ℝ} {d : Option (RIdx n)}
    {Q : Set (Point n)} {u : Point n → ℝ}
    (hAtoms : ∀ β ∈ P.atoms, F05GoodDiffOn T d (F05GoodWord T β u) Q) :
    F05GoodDiffOn T d (P.eval T u) Q := by
  revert hAtoms
  induction P with
  | constant c =>
    intro hAtoms z hz
    cases d with
    | none => exact differentiableWithinAt_const c
    | some j => exact differentiableAt_const c
  | atom β =>
    intro hAtoms
    exact hAtoms β (by simp only [atoms,List.mem_singleton])
  | add P1 P2 ih1 ih2 =>
    intro hAtoms
    have h1 := ih1 (fun β hβ => hAtoms β (List.mem_append_left _ hβ))
    have h2 := ih2 (fun β hβ => hAtoms β (List.mem_append_right _ hβ))
    intro z hz
    cases d with
    | none => exact (h1 z hz).add (h2 z hz)
    | some j => exact (h1 z hz).add (h2 z hz)
  | mul P1 P2 ih1 ih2 =>
    intro hAtoms
    exact F05_good_diff_mul (ih1 (fun β hβ => hAtoms β (List.mem_append_left _ hβ)))
      (ih2 (fun β hβ => hAtoms β (List.mem_append_right _ hβ)))

theorem partial_eval (P : F05GoodPolynomial n) {T : ℝ} {d : Option (RIdx n)}
    {Q : Set (Point n)} {u : Point n → ℝ}
    (hAtoms : ∀ β ∈ P.atoms, F05GoodDiffOn T d (F05GoodWord T β u) Q)
    {z : Point n} (hz : z ∈ Q) :
    F05GoodPartial T d (P.eval T u) z = (P.derivative d).eval T u z := by
  revert hAtoms
  induction P with
  | constant c =>
    intro hAtoms
    cases d with
    | none => simp only [eval,derivative,F05GoodPartial,derivWithin_fun_const,Pi.zero_apply]
    | some j => simp only [eval,derivative,F05GoodPartial,deriv_const]
  | atom β => intro hAtoms; rfl
  | add P1 P2 ih1 ih2 =>
    intro hAtoms
    have hA1 : ∀ β ∈ P1.atoms, F05GoodDiffOn T d (F05GoodWord T β u) Q :=
      fun β hβ => hAtoms β (List.mem_append_left _ hβ)
    have hA2 : ∀ β ∈ P2.atoms, F05GoodDiffOn T d (F05GoodWord T β u) Q :=
      fun β hβ => hAtoms β (List.mem_append_right _ hβ)
    change F05GoodPartial T d (fun p => P1.eval T u p+P2.eval T u p) z =
      (P1.derivative d).eval T u z+(P2.derivative d).eval T u z
    rw [F05_good_partial_add (P1.good_diff hA1) (P2.good_diff hA2) hz,ih1 hA1,ih2 hA2]
  | mul P1 P2 ih1 ih2 =>
    intro hAtoms
    have hA1 : ∀ β ∈ P1.atoms, F05GoodDiffOn T d (F05GoodWord T β u) Q :=
      fun β hβ => hAtoms β (List.mem_append_left _ hβ)
    have hA2 : ∀ β ∈ P2.atoms, F05GoodDiffOn T d (F05GoodWord T β u) Q :=
      fun β hβ => hAtoms β (List.mem_append_right _ hβ)
    change F05GoodPartial T d (fun p => P1.eval T u p*P2.eval T u p) z =
      (P1.derivative d).eval T u z*P2.eval T u z+P1.eval T u z*(P2.derivative d).eval T u z
    rw [F05_good_partial_mul (P1.good_diff hA1) (P2.good_diff hA2) hz,ih1 hA1,ih2 hA2]

theorem holder_eval (P : F05GoodPolynomial n) {T α B : ℝ} {Q : Set (Point n)} {u : Point n → ℝ}
    (hAtoms : ∀ β ∈ P.atoms, HolderBound α Q (F05GoodWord T β u) B) :
    HolderBound α Q (P.eval T u) (P.budget B) := by
  revert hAtoms
  induction P with
  | constant c =>
    intro hAtoms
    simpa only [eval,budget,Real.norm_eq_abs] using holderBound_const α Q c
  | atom β =>
    intro hAtoms
    exact hAtoms β (by simp only [atoms,List.mem_singleton])
  | add P1 P2 ih1 ih2 =>
    intro hAtoms
    exact holderBound_add (ih1 (fun β hβ => hAtoms β (List.mem_append_left _ hβ)))
      (ih2 (fun β hβ => hAtoms β (List.mem_append_right _ hβ)))
  | mul P1 P2 ih1 ih2 =>
    intro hAtoms
    exact holderBound_mul (ih1 (fun β hβ => hAtoms β (List.mem_append_left _ hβ)))
      (ih2 (fun β hβ => hAtoms β (List.mem_append_right _ hβ)))

end F05GoodPolynomial
end Yau.Proofs.F05Aux
