import Yau.Proofs.C05InverseEnergyNaturalityAlgebra

/-! The actual weighted real Hessian energy is invariant under every invertible
real change of frame. The total matrix inverses need no extra invertibility hypothesis. -/
noncomputable section
open scoped Matrix
namespace Yau.Proofs.C05HessianEnergyAux
open Yau.Proofs.C05Aux
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def hessianEnergy (G A B : Matrix ι ι ℝ) : ℝ :=
  (1/2 : ℝ)*(G⁻¹*B*A⁻¹*Bᵀ).trace

theorem hessianEnergy_congruence (G A B J : Matrix ι ι ℝ) (hJ : J.det ≠ 0) :
    hessianEnergy (Jᵀ*G*J) (Jᵀ*A*J) (Jᵀ*B*J)=hessianEnergy G A B := by
  let GI := (Jᵀ*G*J)⁻¹
  let AI := (Jᵀ*A*J)⁻¹
  have hG := inverseMatrix_congruence J G hJ
  have hA := inverseMatrix_congruence J A hJ
  unfold hessianEnergy
  congr 1
  simp only [Matrix.transpose_mul,Matrix.transpose_transpose]
  calc
    _ = ((GI*(Jᵀ*B*J)*AI*(Jᵀ*Bᵀ))*J).trace := by
      simp only [GI,AI,Matrix.mul_assoc]
    _ = (J*(GI*(Jᵀ*B*J)*AI*(Jᵀ*Bᵀ))).trace := Matrix.trace_mul_comm _ _
    _ = ((J*GI*Jᵀ)*B*(J*AI*Jᵀ)*Bᵀ).trace := by simp only [Matrix.mul_assoc]
    _ = _ := by
      change ((J*(Jᵀ*G*J)⁻¹*Jᵀ)*B*(J*(Jᵀ*A*J)⁻¹*Jᵀ)*Bᵀ).trace = _
      rw [hG,hA]

theorem hessianTrace_eq_sum (G A B : Matrix ι ι ℝ) (hG : G.IsSymm) :
    (G⁻¹*B*A⁻¹*Bᵀ).trace =
      ∑ i, ∑ j, G⁻¹ i j * (B i ⬝ᵥ (A⁻¹*ᵥ B j)) := by
  have hM (i j : ι) : (B*A⁻¹*Bᵀ) i j=B i ⬝ᵥ (A⁻¹*ᵥ B j) := by
    rw [Matrix.mul_assoc]
    simp only [Matrix.mul_apply,Matrix.transpose_apply,dotProduct,Matrix.mulVec]
  calc
    _ = ((B*A⁻¹*Bᵀ)*G⁻¹).trace := by
      calc
        _ = (G⁻¹*(B*A⁻¹*Bᵀ)).trace := by simp only [Matrix.mul_assoc]
        _ = _ := Matrix.trace_mul_comm _ _
    _ = ∑ i, ∑ j, (B*A⁻¹*Bᵀ) i j * G⁻¹ j i := rfl
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [hM,hG.inv.apply j i]
      ring

end Yau.Proofs.C05HessianEnergyAux
