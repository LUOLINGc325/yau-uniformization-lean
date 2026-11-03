import Yau.LeafProofs.L23ContractionWordSlots
import Yau.LeafProofs.L23TensorTraceNorm

/-! A Word2 evaluation is exactly a reindexed tensor product followed
by two genuine inverse-metric traces. -/

noncomputable section
open scoped Matrix

namespace Yau.LeafProofs.L23Aux
set_option backward.isDefEq.respectTransparency false

def pairAssignment {ι : Type*} (a b c d : ι) : PairLabel → ι :=
  fun p => ![![a,b],![c,d]] p.1 p.2

def pairAssignmentEquiv (ι : Type*) : (ι × ι × ι × ι) ≃ (PairLabel → ι) where
  toFun x := pairAssignment x.1 x.2.1 x.2.2.1 x.2.2.2
  invFun f := (f (0,0),f (0,1),f (1,0),f (1,1))
  left_inv x := by rcases x with ⟨a,b,c,d⟩; rfl
  right_inv f := by
    funext p
    rcases p with ⟨i,j⟩
    fin_cases i <;> fin_cases j <;> rfl

theorem sum_pairAssignment {ι : Type*} [Fintype ι] (f : (PairLabel → ι) → ℝ) :
    (∑ a, f a)=∑ a, ∑ b, ∑ c, ∑ d, f (pairAssignment a b c d) := by
  calc
    _=∑ x : ι × ι × ι × ι, f (pairAssignment x.1 x.2.1 x.2.2.1 x.2.2.2) :=
      ((pairAssignmentEquiv ι).sum_comp f).symm
    _=_ := by simp only [Fintype.sum_prod_type]

def prependFour {ι : Type*} {q : ℕ} (a b c d : ι) (v : Fin q → ι) : Fin (q+4) → ι :=
  Fin.cons a (Fin.cons b (Fin.cons c (Fin.cons d v)))

theorem prependFour_wordSlotIndex {ι : Type*} {q : ℕ}
    (a b c d : ι) (v : Fin q → ι) (j : SlotLabel q) :
    prependFour a b c d v (wordSlotIndex q j)=Sum.elim v (pairAssignment a b c d) j := by
  cases j with
  | inl j => rw [wordSlotIndex_free]; rfl
  | inr p =>
      rcases p with ⟨i,j⟩
      fin_cases i <;> fin_cases j <;> rfl

namespace Word2
variable {r s q : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem wiredProduct_prependFour (w : Word2 r s q)
    (A : (Fin r → ι) → ℝ) (B : (Fin s → ι) → ℝ) (a b c d : ι) (v : Fin q → ι) :
    w.wiredProduct A B (prependFour a b c d v)=
      A (fun j => Sum.elim v (pairAssignment a b c d) (w.wire (Sum.inl j)))*
        B (fun j => Sum.elim v (pairAssignment a b c d) (w.wire (Sum.inr j))) := by
  rw [wiredProduct_apply]
  simp only [prependFour_wordSlotIndex]

theorem eval_quad (w : Word2 r s q) (H : Matrix ι ι ℝ)
    (A : (Fin r → ι) → ℝ) (B : (Fin s → ι) → ℝ) (v : Fin q → ι) :
    w.eval H A B v=∑ a, ∑ b, ∑ c, ∑ d,
      A (fun j => Sum.elim v (pairAssignment a b c d) (w.wire (Sum.inl j)))*
        B (fun j => Sum.elim v (pairAssignment a b c d) (w.wire (Sum.inr j)))*H a b*H c d := by
  unfold eval
  rw [sum_pairAssignment]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro d _
  simp [Fin.prod_univ_two,pairAssignment,mul_assoc]

theorem eval_eq_two_traces (w : Word2 r s q) (H : Matrix ι ι ℝ)
    (A : (Fin r → ι) → ℝ) (B : (Fin s → ι) → ℝ) :
    w.eval H A B=tensorMetricTrace H (tensorMetricTrace H (w.wiredProduct A B)) := by
  funext v
  unfold eval
  rw [sum_pairAssignment]
  have hweight (a b c d : ι) :
      (∏ p : Fin 2, H (pairAssignment a b c d (p,0)) (pairAssignment a b c d (p,1)))=
        H a b*H c d := by simp [Fin.prod_univ_two,pairAssignment]
  simp only [hweight,tensorMetricTrace,Finset.mul_sum]
  conv_rhs =>
    arg 2
    ext c
    rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  conv_rhs =>
    arg 2
    ext a
    arg 2
    ext c
    rw [Finset.sum_comm]
  conv_rhs =>
    arg 2
    ext a
    rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro d _
  change _=H c d*(H a b*w.wiredProduct A B (prependFour a b c d v))
  rw [wiredProduct_prependFour]
  ring

end Word2

end Yau.LeafProofs.L23Aux
