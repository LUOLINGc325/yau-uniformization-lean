import Yau.LeafProofs.L23TensorLocalAlgebra

/-! Permuting every old covariant slot commutes with the original derivative. -/

noncomputable section
open Filter
open scoped Topology Matrix

namespace Yau.LeafProofs.L23Aux
set_option backward.isDefEq.respectTransparency false

theorem update_comp_perm {ι : Type*} [DecidableEq ι] {r : ℕ}
    (v : Fin r → ι) (e : Equiv.Perm (Fin r)) (s : Fin r) (b : ι) :
    (Function.update v (e s) b) ∘ e=Function.update (v ∘ e) s b := by
  funext a
  by_cases has : a=s
  · subst a
    simp only [Function.comp_apply,Function.update_self]
  · have he : e a ≠ e s := fun hh => has (e.injective hh)
    simp only [Function.comp_apply,Function.update_of_ne has,Function.update_of_ne he]

theorem tensorConnectionAction_permute {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (D : Matrix ι ι ℝ) (A : (Fin r → ι) → ℝ) (v : Fin r → ι)
    (e : Equiv.Perm (Fin r)) :
    tensorConnectionAction D (fun w => A (w ∘ e)) v=
      tensorConnectionAction D A (v ∘ e) := by
  unfold tensorConnectionAction
  rw [←Equiv.sum_comp e (fun s => tensorSlotAction s D (fun w => A (w ∘ e)) v)]
  apply Finset.sum_congr rfl
  intro s _
  simp only [tensorSlotAction,update_comp_perm,Function.comp_apply]

variable {n r : ℕ} {M : ComplexManifold n}

theorem covariantD_permute_cons (h : HermitianField M) (c : M.Carrier)
    (A : ComplexVector n → CovTensor n r) (e : Equiv.Perm (Fin r))
    (z : ComplexVector n) (i : RIdx n) (v : Fin r → RIdx n) :
    covariantD h c (fun w v => A w (v ∘ e)) z (Fin.cons i v)=
      covariantD h c A z (Fin.cons i (v ∘ e)) := by
  rw [covariantD_cons,covariantD_cons,tensorConnectionAction_permute]

theorem covariantD_signedPermutation_at (h : HermitianField M) (c : M.Carrier)
    (A : ComplexVector n → CovTensor n r) (e : Equiv.Perm (Fin r))
    (z : ComplexVector n) (α : ℝ)
    (hA : ∀ v, DifferentiableAt ℝ (fun w => A w v) z)
    (hSym : (fun w v => A w (v ∘ e))=ᶠ[𝓝 z] (fun w v => α*A w v))
    (i : RIdx n) (v : Fin r → RIdx n) :
    covariantD h c A z (Fin.cons i (v ∘ e))=α*covariantD h c A z (Fin.cons i v) := by
  have hD := covariantD_eventuallyEq h c _ _ z hSym
  rw [covariantD_const_mul_at h c A z hA α] at hD
  have hp := congrFun hD (Fin.cons i v)
  rw [covariantD_permute_cons] at hp
  exact hp

end Yau.LeafProofs.L23Aux
