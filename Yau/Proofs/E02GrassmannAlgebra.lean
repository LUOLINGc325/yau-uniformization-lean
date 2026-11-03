import Yau.Proofs.E02MatrixBasic

open Matrix
open scoped Matrix ComplexOrder
noncomputable section
namespace Yau.NodeProofs.E02Aux
open Yau Yau.Blueprint

def projectorTangent {n m : ℕ} (M Z : Rect n m) : Herm m :=
  Mᴴ*(M*Mᴴ)⁻¹*Z*(1-rowProjector M)

theorem one_sub_rowProjector_idempotent {n m : ℕ} (M : Rect n m) (hM : (M*Mᴴ).PosDef) :
    (1-rowProjector M)*(1-rowProjector M) = 1-rowProjector M := by
  have hPP := rowProjector_idempotent M hM
  calc
    _ = 1-rowProjector M-rowProjector M+rowProjector M*rowProjector M := by noncomm_ring
    _ = _ := by rw [hPP]; abel

theorem rowProjector_mul_adjoint_inv {n m : ℕ} (M : Rect n m) (hM : (M*Mᴴ).PosDef) :
    rowProjector M*Mᴴ*(M*Mᴴ)⁻¹ = Mᴴ*(M*Mᴴ)⁻¹ := by
  have hBA : (M*Mᴴ)⁻¹*(M*Mᴴ) = 1 :=
    Matrix.nonsing_inv_mul _ (hM.isUnit.map Matrix.detMonoidHom)
  unfold rowProjector
  calc
    _ = Mᴴ*((M*Mᴴ)⁻¹*(M*Mᴴ))*(M*Mᴴ)⁻¹ := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hBA]; simp

theorem projectorTangent_relations {n m : ℕ} (M Z : Rect n m) (hM : (M*Mᴴ).PosDef) :
    rowProjector M*projectorTangent M Z = projectorTangent M Z ∧
    projectorTangent M Z*(1-rowProjector M) = projectorTangent M Z ∧
    projectorTangent M Z*rowProjector M = 0 ∧
    (1-rowProjector M)*projectorTangent M Z = 0 := by
  let P := rowProjector M
  let Q : Herm m := 1-P
  let S := projectorTangent M Z
  have hPM := rowProjector_mul_adjoint_inv M hM
  have hQQ : Q*Q = Q := one_sub_rowProjector_idempotent M hM
  have hQP : Q*P = 0 := by
    dsimp [Q]
    rw [Matrix.sub_mul,Matrix.one_mul,rowProjector_idempotent M hM,sub_self]
  have hPS : P*S = S := by
    change P*(Mᴴ*(M*Mᴴ)⁻¹*Z*Q) = Mᴴ*(M*Mᴴ)⁻¹*Z*Q
    calc
      _ = (P*Mᴴ*(M*Mᴴ)⁻¹)*Z*Q := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hPM]
  have hSQ : S*Q = S := by
    change (Mᴴ*(M*Mᴴ)⁻¹*Z*Q)*Q = Mᴴ*(M*Mᴴ)⁻¹*Z*Q
    rw [Matrix.mul_assoc,hQQ]
  have hSP : S*P = 0 := by
    change (Mᴴ*(M*Mᴴ)⁻¹*Z*Q)*P = 0
    rw [Matrix.mul_assoc,hQP,Matrix.mul_zero]
  have hQS : Q*S = 0 := by
    change (1-P)*S = 0
    rw [Matrix.sub_mul,Matrix.one_mul,hPS,sub_self]
  exact ⟨hPS,hSQ,hSP,hQS⟩

end Yau.NodeProofs.E02Aux
