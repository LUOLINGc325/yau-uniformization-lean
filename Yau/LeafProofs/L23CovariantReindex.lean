import Yau.LeafProofs.L23CovariantPermutation

/-! Reindexing covariant slots along an actual finite equivalence commutes
with the original derivative, without introducing rank casts. -/

noncomputable section
open scoped Matrix

namespace Yau.LeafProofs.L23Aux
set_option backward.isDefEq.respectTransparency false

theorem update_comp_equiv {α β ι : Type*} [DecidableEq α] [DecidableEq β]
    (v : β → ι) (e : α ≃ β) (s : α) (b : ι) :
    (Function.update v (e s) b) ∘ e=Function.update (v ∘ e) s b := by
  funext a
  by_cases has : a=s
  · subst a
    simp only [Function.comp_apply,Function.update_self]
  · have he : e a ≠ e s := fun hh => has (e.injective hh)
    simp only [Function.comp_apply,Function.update_of_ne has,Function.update_of_ne he]

theorem tensorConnectionAction_reindex {ι : Type*} [Fintype ι] [DecidableEq ι]
    {r s : ℕ} (D : Matrix ι ι ℝ) (A : (Fin r → ι) → ℝ) (v : Fin s → ι)
    (e : Fin r ≃ Fin s) :
    tensorConnectionAction D (fun w => A (w ∘ e)) v=
      tensorConnectionAction D A (v ∘ e) := by
  unfold tensorConnectionAction
  rw [←Equiv.sum_comp e (fun j => tensorSlotAction j D (fun w => A (w ∘ e)) v)]
  apply Finset.sum_congr rfl
  intro j _
  simp only [tensorSlotAction,update_comp_equiv,Function.comp_apply]

variable {n r s : ℕ} {M : ComplexManifold n}

theorem covariantD_reindex_cons (h : HermitianField M) (c : M.Carrier)
    (A : ComplexVector n → CovTensor n r) (e : Fin r ≃ Fin s)
    (z : ComplexVector n) (i : RIdx n) (v : Fin s → RIdx n) :
    covariantD h c (fun w v => A w (v ∘ e)) z (Fin.cons i v)=
      covariantD h c A z (Fin.cons i (v ∘ e)) := by
  rw [covariantD_cons,covariantD_cons,tensorConnectionAction_reindex]

end Yau.LeafProofs.L23Aux
