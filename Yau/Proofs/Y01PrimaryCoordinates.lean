import Yau.Proofs.Y01CoordinateGerms

/-! Exact matrix identities connect the original normalized regular
transition with the same primary coordinate derivatives used in H. -/

noncomputable section

attribute [local instance] Classical.propDecidable

namespace Yau.Proofs.Y01Aux

open Yau.Blueprint Yau.Blueprint.Alignment Yau.Proofs.Y02Aux

variable {n : ℕ}

theorem unitary_conjTranspose_inverse {U : Herm n} (hU : Unitary U) :
    U.conjTranspose⁻¹ = U := Matrix.inv_eq_left_inv hU.2

theorem primary_regular_inverse {reg : ℕ → Prop} {E : Frames n} {L : Changes n}
    {k : ℕ} (hk : reg k) (hU : Unitary (E.start k)) :
    (primaryDerivative reg E L k)⁻¹ = E.start k * (L.minus k)⁻¹ := by
  classical
  simp only [primaryDerivative, hk, ite_true, Matrix.mul_inv_rev,
    unitary_conjTranspose_inverse hU]

theorem linearPoly_eval_mul (A B : Herm n) (z : ComplexVector n) :
    (linearPoly (A * B)).eval z = (linearPoly A).eval ((linearPoly B).eval z) := by
  rw [← linearPoly_comp]
  exact polyMap_eval_comp _ _ _

theorem normalized_primary_transition
    {F : ℝ → ℝ → ComplexVector n → ComplexVector n} {tk : ℕ → ℝ}
    {A Ainv : ℕ → PolyMap n} {E : Frames n} {L : Changes n} {reg : ℕ → Prop}
    {k : ℕ} (hk : reg k) (hstart : Unitary (E.start k))
    (hfinish : Unitary (E.finish k)) (hplus : IsUnit (L.plus k)) :
    (linearPoly (primaryDerivative reg E L (k + 1))).eval ∘ (A (k + 1)).eval ∘
        F (tk k) (tk (k + 1)) ∘ (Ainv k).eval ∘
        (linearPoly (primaryDerivative reg E L k)⁻¹).eval =
      (linearPoly (if reg (k + 1) then alignedJump E L k else 1)).eval ∘
        normalizedRegularTransition F tk A Ainv E L k := by
  funext z
  rw [primary_next_factor hk hfinish hplus, primary_regular_inverse hk hstart]
  simp only [Function.comp_apply, linearPoly_eval_mul]
  simp only [linearPoly_eval, normalizedRegularTransition, map_mul, ContinuousLinearMap.mul_apply]

end Yau.Proofs.Y01Aux
