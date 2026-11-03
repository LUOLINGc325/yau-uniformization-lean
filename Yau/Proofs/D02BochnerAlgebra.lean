import Yau.Proofs.D02DualFirstDerivative

/-! The exact algebra following differentiation of the actual lowering
identity. The negative metric term is kept with its order of factors. -/

noncomputable section
open scoped Matrix ComplexOrder
namespace Yau.NodeProofs.D02Aux
open Yau

variable {r : ℕ}

theorem dualBochner_loweringAlgebra (D A B C : Matrix (Fin r) (Fin r) ℂ)
    (hD : D.PosDef) (t p tbar pbar : Fin r → ℂ)
    (hbar : B *ᵥ t + D *ᵥ tbar = 0)
    (hsecond : B *ᵥ p + D *ᵥ pbar = -(C *ᵥ t + A *ᵥ tbar)) :
    star p ⬝ᵥ D *ᵥ p + star t ⬝ᵥ (B *ᵥ p + D *ᵥ pbar) =
      star p ⬝ᵥ D *ᵥ p + star t ⬝ᵥ (-C + A * D⁻¹ * B) *ᵥ t := by
  have hbar' : D *ᵥ tbar = -(B *ᵥ t) := by
    apply eq_neg_iff_add_eq_zero.mpr
    simpa only [add_comm] using hbar
  have hsolve : tbar = -(D⁻¹ *ᵥ (B *ᵥ t)) := by
    calc
      tbar = D⁻¹ *ᵥ (D *ᵥ tbar) := by
        rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul D (hD.isUnit.map Matrix.detMonoidHom),
          Matrix.one_mulVec]
      _ = D⁻¹ *ᵥ (-(B *ᵥ t)) := congrArg _ hbar'
      _ = _ := Matrix.mulVec_neg _ _
  have hvec : -(C *ᵥ t + A *ᵥ tbar) = (-C + A * D⁻¹ * B) *ᵥ t := by
    rw [hsolve]
    simp only [Matrix.add_mulVec, Matrix.neg_mulVec, Matrix.mulVec_neg,
      ← Matrix.mulVec_mulVec]
    abel
  rw [hsecond, hvec]

end Yau.NodeProofs.D02Aux
