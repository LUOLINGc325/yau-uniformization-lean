import Yau.Proofs.F01WirtingerCoordinateChain

/-! Constant complex changes of frame transport the actual first Wirtinger
matrix jet, with entrywise differentiability only. -/
noncomputable section
open scoped Matrix
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs
variable {n : ℕ}

theorem wirt_matrix_congruence_entry (A : Matrix (Fin n) (Fin n) ℂ)
    (G : ComplexVector n → Matrix (Fin n) (Fin n) ℂ)
    (T : ComplexVector n → ComplexVector n) (z v : ComplexVector n)
    (hT : DifferentiableAt ℂ T z)
    (hG : ∀ p q, DifferentiableAt ℝ (fun y => G y p q) (T z)) (i j : Fin n) :
    wirt (fun w => (Aᴴ * G (T w) * A) i j) z v =
      ∑ q, ∑ p, star (A p i) *
        wirt (fun y => G y p q) (T z) (fderiv ℂ T z v) * A q j := by
  have hentry (p q : Fin n) : DifferentiableAt ℝ (fun w => G (T w) p q) z :=
    (hG p q).comp z (hT.restrictScalars ℝ)
  have hterm (p q : Fin n) :
      DifferentiableAt ℝ (fun w => star (A p i) * G (T w) p q * A q j) z :=
    ((hentry p q).const_mul _).mul_const _
  have hrow (q : Fin n) :
      DifferentiableAt ℝ (fun w => ∑ p, star (A p i) * G (T w) p q * A q j) z :=
    DifferentiableAt.fun_sum (u := Finset.univ) (fun p _ => hterm p q)
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
  have ho := L14Aux.wirt_sum_fun Finset.univ
    (fun q w => ∑ p, star (A p i) * G (T w) p q * A q j) z v (fun q _ => hrow q)
  rw [ho]
  apply Finset.sum_congr rfl
  intro q hq
  have hi := L14Aux.wirt_sum_fun Finset.univ
    (fun p w => star (A p i) * G (T w) p q * A q j) z v (fun p _ => hterm p q)
  rw [hi]
  apply Finset.sum_congr rfl
  intro p hp
  rw [wirt_mul_const_rule _ ((hentry p q).const_mul _),
    wirt_const_mul_rule _ (hentry p q),
    wirt_comp_complex_differentiable T (fun y => G y p q) z v hT (hG p q)]

end Yau.NodeProofs.F01Aux
