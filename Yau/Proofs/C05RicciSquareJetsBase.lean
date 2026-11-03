import Yau.Proofs.C05RicciSquareJetsTerms

/-! The actual initial wiring pairs the two slots of each Ricci tensor. -/
noncomputable section
open scoped Topology Manifold ContDiff Matrix
namespace Yau.Proofs.C05RicciSquareJetsAux
open Yau Yau.Proofs.C05Aux Yau.LeafProofs.L12Aux Yau.LeafProofs.L23Aux

def ricciSquareWord : Word2 2 2 0 where
  wire :=
    { toFun := Sum.elim (fun i => .inr (i,0)) (fun j => .inr (j,1))
      invFun := Sum.elim Fin.elim0 (fun p => Fin.cases (.inl p.1) (fun _ => .inr p.1) p.2)
      left_inv := by intro s; cases s <;> rfl
      right_inv := by
        intro s
        cases s with
        | inl i => exact Fin.elim0 i
        | inr p => rcases p with ⟨i,j⟩; fin_cases j <;> rfl }

def ricciSquareTermZero : RicciTerm 0 where
  leftOrder := 0
  rightOrder := 0
  word := ricciSquareWord

def pairFunctionEquiv (ι : Type*) : (PairLabel → ι) ≃ ((Fin 2 → ι) × (Fin 2 → ι)) where
  toFun a := (fun i => a (i,0),fun i => a (i,1))
  invFun p a := Fin.cases (p.1 a.1) (fun _ => p.2 a.1) a.2
  left_inv := by intro a; funext p; rcases p with ⟨i,j⟩; fin_cases j <;> rfl
  right_inv := by intro p; rfl

theorem ricciSquareWord_eval {n : ℕ} (G : Matrix (RIdx n) (RIdx n) ℝ)
    (A : CovTensor n 2) (v : Fin 0 → RIdx n) :
    ricciSquareWord.eval G⁻¹ A A v = covTensorNormSq G A := by
  unfold Word2.eval covTensorNormSq
  rw [← (pairFunctionEquiv (RIdx n)).symm.sum_comp]
  simp only [Fintype.sum_prod_type, pairFunctionEquiv, ricciSquareWord, Equiv.coe_fn_symm_mk,
    Sum.elim_inr,Fin.cases_zero,Fin.cases_succ,Fin.prod_univ_succ,Fin.prod_univ_zero,mul_one]
  rfl

end Yau.Proofs.C05RicciSquareJetsAux
