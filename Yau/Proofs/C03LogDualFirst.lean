import Yau.Proofs.C03LogDualBasic

/-! The first Wirtinger derivative keeps the actual inverse-transpose pairing. -/
noncomputable section
open scoped Topology ContDiff Matrix ComplexOrder
open Set Filter
namespace Yau.Proofs.C03Aux.LogDual
open Yau Yau.Blueprint Yau.NodeProofs.E01Aux Yau.Blueprint.V03Proof
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5
variable {n : ℕ}

theorem wirt_constant_quadratic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (K : E → Herm n) (z a : E)
    (hK : ∀ i j, DifferentiableAt ℝ (fun w => K w i j) z)
    (xi : ComplexVector n) :
    wirt (fun w => star (WithLp.ofLp xi) ⬝ᵥ (K w *ᵥ WithLp.ofLp xi)) z a =
      matrixPairing (complexMatrixWirt K z a) xi xi := by
  let F : Fin n → Fin n → E → ℂ := fun i j w => star (xi i) * K w i j * xi j
  have hF (i j : Fin n) : DifferentiableAt ℝ (F i j) z :=
    ((differentiableAt_const (star (xi i))).fun_mul (hK i j)).fun_mul (differentiableAt_const (xi j))
  have hFc (i : Fin n) : DifferentiableAt ℝ (fun w => ∑ j, F i j w) z :=
    DifferentiableAt.fun_sum (u := Finset.univ) (fun j _ => hF i j)
  have hpair : (fun w => star (WithLp.ofLp xi) ⬝ᵥ (K w *ᵥ WithLp.ofLp xi)) =
      (fun w => ∑ i, ∑ j, F i j w) := by
    funext w
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum, F]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hwc (c : ℂ) : wirt (fun _ : E => c) z a = 0 := by simp [wirt]
  have hterm (i j : Fin n) : wirt (F i j) z a =
      star (xi i) * wirt (fun w => K w i j) z a * xi j := by
    dsimp only [F]
    rw [wirt_mul (f := fun w => star (xi i) * K w i j) (g := fun _ : E => xi j)
        ((differentiableAt_const (star (xi i))).fun_mul (hK i j)) (differentiableAt_const (xi j)),
      wirt_mul (f := fun _ : E => star (xi i)) (g := fun w => K w i j)
        (differentiableAt_const (star (xi i))) (hK i j), hwc, hwc]
    ring
  rw [hpair, wirt_sum Finset.univ (fun i w => ∑ j, F i j w) z a (fun i _ => hFc i)]
  simp_rw [wirt_sum Finset.univ (F _) z a (fun j _ => hF _ j), hterm]
  simp only [matrixPairing, complexMatrixWirt, dotProduct, Matrix.mulVec,
    Pi.star_apply, Finset.mul_sum, mul_assoc]

theorem dualSquared_wirt {U : Set (ComplexVector n)} (hU : IsOpen U)
    (H : ComplexVector n → Herm n) (hHerm : ∀ z, (H z).IsHermitian)
    (hH : ∀ i j, ContDiffOn ℝ ∞ (fun z => H z i j) U)
    (hPos : ∀ z ∈ U, (H z).PosDef)
    (z : ComplexVector n) (hz : z ∈ U) (xi a : ComplexVector n) :
    wirt (fun w => (dualSquared H xi w : ℂ)) z a =
      matrixPairing ((H z)⁻¹)ᵀ xi (connectionVector H z xi a) := by
  have hdet : ∀ w ∈ U, (H w).det ≠ 0 := fun w hw => (hPos w hw).det_pos.ne'
  have hK (i j : Fin n) : DifferentiableAt ℝ (fun w => ((H w)⁻¹)ᵀ i j) z :=
    ((entrywise_matrix_inv_contDiffOn hH hdet j i).contDiffAt
      (hU.mem_nhds hz)).differentiableAt (by simp)
  have hHd (i j : Fin n) : DifferentiableAt ℝ (fun w => H w i j) z :=
    ((hH i j).contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)
  have heq : (fun w => (dualSquared H xi w : ℂ)) =
      (fun w => star (WithLp.ofLp xi) ⬝ᵥ (((H w)⁻¹)ᵀ *ᵥ WithLp.ofLp xi)) :=
    funext fun w => dualNormMat_complex_eq (H w) (hHerm w) xi
  rw [heq, wirt_constant_quadratic _ z a hK xi,
    complexMatrixWirt_invTranspose hHd (hdet z hz) a]
  have hc : WithLp.ofLp (connectionVector H z xi a) =
      -(((complexMatrixWirt H z a)ᵀ * ((H z)⁻¹)ᵀ) *ᵥ WithLp.ofLp xi) := rfl
  simp only [matrixPairing, hc, Matrix.neg_mul, Matrix.neg_mulVec,
    Matrix.mulVec_neg, dotProduct_neg, Matrix.mulVec_mulVec, Matrix.mul_assoc]

end Yau.Proofs.C03Aux.LogDual

