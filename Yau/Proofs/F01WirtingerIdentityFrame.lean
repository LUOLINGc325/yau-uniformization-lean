import Yau.Proofs.F01WirtingerCoordinateChain

/-! The genuine first jet of a holomorphic change of frame at an identity
Gram matrix. The conjugate Jacobian contributes no holomorphic derivative. -/
noncomputable section
open scoped Matrix
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs
variable {n : ℕ}

theorem wirt_congruence_at_identity
    (J G : ComplexVector n → Matrix (Fin n) (Fin n) ℂ)
    (z v : ComplexVector n)
    (hJ : ∀ p q, DifferentiableAt ℂ (fun w => J w p q) z)
    (hG : ∀ p q, DifferentiableAt ℝ (fun w => G w p q) z)
    (hJ0 : J z = 1) (hG0 : G z = 1) (i j : Fin n) :
    wirt (fun w => ((J w)ᴴ * G w * J w) i j) z v =
      wirt (fun w => G w i j) z v + wirt (fun w => J w i j) z v := by
  have hJr (p q : Fin n) := (hJ p q).restrictScalars ℝ
  have hstar (p q : Fin n) : wirt (fun w => star (J w p q)) z v = 0 := by
    rw [L14Aux.wirt_star, L14Aux.wirtBar_eq_zero_of_complex_differentiable _ _ _ (hJ p q), star_zero]
  have hterm (p q : Fin n) :
      DifferentiableAt ℝ (fun w => star (J w p i) * G w p q * J w q j) z :=
    (((hJr p i).star).mul (hG p q)).mul (hJr q j)
  have hrow (q : Fin n) :
      DifferentiableAt ℝ (fun w => ∑ p, star (J w p i) * G w p q * J w q j) z :=
    DifferentiableAt.fun_sum (u := Finset.univ) (fun p _ => hterm p q)
  have ht (p q : Fin n) :
      wirt (fun w => star (J w p i) * G w p q * J w q j) z v =
        star (J z p i) * wirt (fun w => G w p q) z v * J z q j +
          star (J z p i) * G z p q * wirt (fun w => J w q j) z v := by
    rw [L14Aux.wirt_mul_rule (fun w : ComplexVector n => star (J w p i) * G w p q)
      (fun w : ComplexVector n => J w q j) z v (((hJr p i).star).mul (hG p q)) (hJr q j),
      L14Aux.wirt_mul_rule (fun w : ComplexVector n => star (J w p i))
        (fun w : ComplexVector n => G w p q) z v (hJr p i).star (hG p q), hstar]
    ring
  have ho := L14Aux.wirt_sum_fun Finset.univ
    (fun q w => ∑ p, star (J w p i) * G w p q * J w q j) z v (fun q _ => hrow q)
  have hi (q : Fin n) := L14Aux.wirt_sum_fun Finset.univ
    (fun p w => star (J w p i) * G w p q * J w q j) z v (fun p _ => hterm p q)
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
  rw [ho]
  simp_rw [hi, ht]
  simp [hJ0, hG0, Matrix.one_apply, Finset.sum_add_distrib]

end Yau.NodeProofs.F01Aux
