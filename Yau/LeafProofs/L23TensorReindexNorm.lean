import Yau.LeafProofs.L23TensorProductNorm

/-! Metric contraction is invariant under a finite equivalence of slots. -/

noncomputable section
open scoped Matrix

namespace Yau.LeafProofs.L23Aux
set_option backward.isDefEq.respectTransparency false

section Finite
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {r s : ℕ}

theorem tensorContraction_reindex (H : Matrix ι ι ℝ)
    (A B : (Fin r → ι) → ℝ) (e : Fin r ≃ Fin s) :
    tensorContraction H (fun v => A (v ∘ e)) (fun v => B (v ∘ e))=
      tensorContraction H A B := by
  let E : (Fin s → ι) ≃ (Fin r → ι) := Equiv.arrowCongr e.symm (Equiv.refl ι)
  unfold tensorContraction
  apply Fintype.sum_equiv E
  intro v
  change (∑ w : Fin s → ι, A (v ∘ e)*B (w ∘ e)*∏ j : Fin s, H (v j) (w j))=
    ∑ w : Fin r → ι, A (v ∘ e)*B w*∏ j : Fin r, H ((v ∘ e) j) (w j)
  apply Fintype.sum_equiv E
  intro w
  change A (v ∘ e)*B (w ∘ e)*(∏ j : Fin s, H (v j) (w j))=
    A (v ∘ e)*B (w ∘ e)*∏ j : Fin r, H (v (e j)) (w (e j))
  rw [Equiv.prod_comp e (fun j => H (v j) (w j))]

end Finite

theorem covTensorNormSq_reindex {n r s : ℕ}
    (G : Matrix (RIdx n) (RIdx n) ℝ) (A : CovTensor n r) (e : Fin r ≃ Fin s) :
    covTensorNormSq G (fun v => A (v ∘ e))=covTensorNormSq G A :=
  tensorContraction_reindex G⁻¹ A A e

end Yau.LeafProofs.L23Aux
