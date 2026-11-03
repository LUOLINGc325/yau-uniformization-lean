import Yau.Proofs.C05HessianEnergyActual
import Yau.Proofs.C05InverseMatrixCompositionBound
import Yau.Proofs.C05ActualInverseEnergyTime
import Yau.Proofs.C05HermitianHessianProjection

/-! Every term in the actual inverse-energy time derivative retains an
undifferentiated scalar differential, with an intrinsic metric budget. -/
noncomputable section
open scoped Topology Manifold ContDiff Matrix
namespace Yau.Proofs.C05Aux
open Yau Blueprint Yau.LeafProofs.L23Aux Yau.Proofs.C05HessianEnergyAux
variable {n : ℕ} {X : KahlerManifold n}
set_option backward.isDefEq.respectTransparency false

theorem sum_matrix_bilinear (K : Matrix (RIdx n) (RIdx n) ℝ)
    (p q : RIdx n → ℝ) :
    (∑ a, ∑ b, K a b*p a*q b) = p ⬝ᵥ (K*ᵥq) := by
  simp only [dotProduct,Matrix.mulVec,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem inverseEnergyTime_sum_eq (A B : Matrix (RIdx n) (RIdx n) ℝ)
    (p q : RIdx n → ℝ) :
    (1/2:ℝ)*(∑ a, ∑ b, ((-(A⁻¹*B*A⁻¹)) a b*p a*p b +
      A⁻¹ a b*q a*p b + A⁻¹ a b*p a*q b)) =
      (1/2:ℝ)*(-(p ⬝ᵥ ((A⁻¹*B*A⁻¹)*ᵥp)) +
        q ⬝ᵥ (A⁻¹*ᵥp) + p ⬝ᵥ (A⁻¹*ᵥq)) := by
  simp only [Finset.sum_add_distrib,Matrix.neg_apply,neg_mul,
    Finset.sum_neg_distrib,sum_matrix_bilinear]

theorem inverseEnergyTime_abs_le (G A B : Matrix (RIdx n) (RIdx n) ℝ)
    (hG : G.PosDef) (p q : CovTensor n 1) :
    |(1/2:ℝ)*(-((fun a => p ![a]) ⬝ᵥ ((A⁻¹*B*A⁻¹)*ᵥ(fun a => p ![a]))) +
      (fun a => q ![a]) ⬝ᵥ (A⁻¹*ᵥ(fun a => p ![a])) +
      (fun a => p ![a]) ⬝ᵥ (A⁻¹*ᵥ(fun a => q ![a])))| ≤
      (1/2:ℝ)*(2*n:ℕ)*metricTensorNorm G (matrixCovTensor (loweredInverseMatrix G A))^2*
        metricTensorNorm G (matrixCovTensor B)*metricTensorNorm G p^2 +
      metricTensorNorm G (matrixCovTensor (loweredInverseMatrix G A))*
        metricTensorNorm G p*metricTensorNorm G q := by
  let C := matrixCovTensor (loweredInverseMatrix G A)
  let T := matrixCovTensor (G*(A⁻¹*B*A⁻¹)*G)
  have ht := covTensorPair_abs_le_norm G hG T (tensorConcatProduct p p)
  have hqp := covTensorPair_abs_le_norm G hG C (tensorConcatProduct q p)
  have hpq := covTensorPair_abs_le_norm G hG C (tensorConcatProduct p q)
  rw [metricTensorNorm_concatProduct G hG] at ht hqp hpq
  have hcomp : metricTensorNorm G T ≤ (2*n:ℕ)*(metricTensorNorm G C)^2*
      metricTensorNorm G (matrixCovTensor B) := by
    dsimp [T,C]
    simpa only [Matrix.mul_assoc] using loweredInverseTimeMatrix_norm_le G A B hG
  have ht' : |covTensorPair G T (tensorConcatProduct p p)| ≤
      ((2*n:ℕ)*(metricTensorNorm G C)^2*metricTensorNorm G (matrixCovTensor B))*
        (metricTensorNorm G p*metricTensorNorm G p) :=
    ht.trans (mul_le_mul_of_nonneg_right hcomp
      (mul_nonneg (metricTensorNorm_nonneg G p) (metricTensorNorm_nonneg G p)))
  have habs := (abs_add_le (-covTensorPair G T (tensorConcatProduct p p) +
    covTensorPair G C (tensorConcatProduct q p))
    (covTensorPair G C (tensorConcatProduct p q))).trans
      (add_le_add (abs_add_le _ _) le_rfl)
  rw [abs_neg] at habs
  have htq := habs.trans (add_le_add (add_le_add ht' hqp) hpq)
  have heT := metric_pair_lowered_matrix G (A⁻¹*B*A⁻¹) hG p p
  have heqp := metric_pair_lowered_matrix G A⁻¹ hG q p
  have hepq := metric_pair_lowered_matrix G A⁻¹ hG p q
  change covTensorPair G T _ = _ at heT
  change covTensorPair G C _ = _ at heqp hepq
  rw [←heT,←heqp,←hepq,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<1/2)]
  apply (mul_le_mul_of_nonneg_left htq (by norm_num : (0:ℝ)≤1/2)).trans_eq
  dsimp [C]
  ring

end Yau.Proofs.C05Aux
