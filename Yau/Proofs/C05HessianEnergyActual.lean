import Yau.Proofs.C05HessianEnergyMatrix
import Yau.Proofs.C05ActualInverseEnergyLaplacian

/-! The leading term of the actual inverse energy is the same real trace
energy, with both physical factors one-half retained. -/
noncomputable section
open scoped Matrix Manifold Topology ContDiff
namespace Yau.Proofs.C05HessianEnergyAux
open Yau Yau.Proofs.C05Aux Yau.LeafProofs.L23Aux Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false

theorem loweredMatrix_bilinear (G K : Matrix (RIdx n) (RIdx n) ℝ)
    (hG : G.IsSymm) (hdet : G.det ≠ 0) (p q : RIdx n → ℝ) :
    (G⁻¹*ᵥp) ⬝ᵥ ((G*K*G)*ᵥ(G⁻¹*ᵥq)) = p ⬝ᵥ (K*ᵥq) := by
  have hGp : G*ᵥ(G⁻¹*ᵥp)=p := by
    rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv G
      (isUnit_iff_ne_zero.mpr hdet),Matrix.one_mulVec]
  have hGq : G*ᵥ(G⁻¹*ᵥq)=q := by
    rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv G
      (isUnit_iff_ne_zero.mpr hdet),Matrix.one_mulVec]
  rw [←Matrix.mulVec_mulVec,←Matrix.mulVec_mulVec,hGq,
    Matrix.dotProduct_mulVec,←Matrix.mulVec_transpose,hG.eq,hGp]

theorem loweredInverseMatrix_bilinear (G A : Matrix (RIdx n) (RIdx n) ℝ)
    (hG : G.IsSymm) (hdet : G.det ≠ 0) (p q : RIdx n → ℝ) :
    (G⁻¹*ᵥp) ⬝ᵥ (loweredInverseMatrix G A*ᵥ(G⁻¹*ᵥq)) = p ⬝ᵥ (A⁻¹*ᵥq) :=
  loweredMatrix_bilinear G A⁻¹ hG hdet p q

 theorem matrixCovTensor_bilinear (B : Matrix (RIdx n) (RIdx n) ℝ) (u v : RIdx n → ℝ) :
    tensorEvaluation (matrixCovTensor B) ![u,v] = u ⬝ᵥ (B*ᵥv) := by
  simp only [tensorEvaluation,tensorProduct,matrixCovTensor,sum_tensor_cons,
    Fin.prod_univ_succ,Fin.prod_univ_zero,Fin.cons_zero,Fin.cons_succ,
    mul_one,Fintype.sum_unique,dotProduct,Matrix.mulVec,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  have h1 : (1 : Fin 2)=(0 : Fin 1).succ := rfl
  simp only [h1,Fin.cons_succ,Fin.cons_zero,Matrix.cons_val_succ,Matrix.cons_val_zero,Matrix.cons_val_one]
  ring

 theorem loweredMatrix_pair_bilinear (G K : Matrix (RIdx n) (RIdx n) ℝ)
    (hG : G.IsSymm) (hdet : G.det ≠ 0) (p q : RIdx n → ℝ) :
    covTensorPair G (matrixCovTensor (G*K*G))
      (tensorConcatProduct (fun u : Fin 1 → RIdx n => p (u 0)) (fun u : Fin 1 → RIdx n => q (u 0))) = p ⬝ᵥ (K*ᵥq) := by
  let V : Fin 2 → RIdx n → ℝ := ![G⁻¹*ᵥp,G⁻¹*ᵥq]
  have hGp : G*ᵥ(G⁻¹*ᵥp)=p := by
    rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv G
      (isUnit_iff_ne_zero.mpr hdet),Matrix.one_mulVec]
  have hGq : G*ᵥ(G⁻¹*ᵥq)=q := by
    rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv G
      (isUnit_iff_ne_zero.mpr hdet),Matrix.one_mulVec]
  have hPQ : tensorProduct (fun j => G*ᵥV j) =
      tensorConcatProduct (fun u : Fin 1 → RIdx n => p (u 0)) (fun u : Fin 1 → RIdx n => q (u 0)) := by
    funext w
    simp only [tensorProduct,Fin.prod_univ_two]
    change (G*ᵥ(G⁻¹*ᵥp)) (w 0)*(G*ᵥ(G⁻¹*ᵥq)) (w 1)=p (w 0)*q (w 1)
    rw [hGp,hGq]
  have H := tensorEvaluation_eq_contraction G G⁻¹
    (Matrix.nonsing_inv_mul G (isUnit_iff_ne_zero.mpr hdet))
    (matrixCovTensor (G*K*G)) V
  change covTensorPair G (matrixCovTensor (G*K*G))
    (tensorProduct (fun j => G*ᵥV j)) = tensorEvaluation (matrixCovTensor (G*K*G)) V at H
  rw [hPQ] at H
  rw [H]
  change tensorEvaluation (matrixCovTensor (G*K*G)) ![G⁻¹*ᵥp,G⁻¹*ᵥq] = _
  rw [matrixCovTensor_bilinear]
  exact loweredMatrix_bilinear G K hG hdet p q

 theorem loweredInverseMatrix_pair_bilinear (G A : Matrix (RIdx n) (RIdx n) ℝ)
    (hG : G.IsSymm) (hdet : G.det ≠ 0) (p q : RIdx n → ℝ) :
    covTensorPair G (matrixCovTensor (loweredInverseMatrix G A))
      (tensorConcatProduct (fun u : Fin 1 → RIdx n => p (u 0))
        (fun u : Fin 1 → RIdx n => q (u 0))) = p ⬝ᵥ (A⁻¹*ᵥq) :=
  loweredMatrix_pair_bilinear G A⁻¹ hG hdet p q

 theorem metric_pair_lowered_matrix (G K : Matrix (RIdx n) (RIdx n) ℝ)
    (hG : G.PosDef) (p q : CovTensor n 1) :
    covTensorPair G (matrixCovTensor (G*K*G)) (tensorConcatProduct p q) =
      (fun a => p ![a]) ⬝ᵥ (K*ᵥ(fun a => q ![a])) := by
  have hsym : G.IsSymm := by
    change Gᵀ=G
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hG.isHermitian.eq
  have hp : (fun u : Fin 1 → RIdx n => p ![u 0])=p := by
    funext u
    congr 1
    funext j
    fin_cases j
    rfl
  have hq : (fun u : Fin 1 → RIdx n => q ![u 0])=q := by
    funext u
    congr 1
    funext j
    fin_cases j
    rfl
  have H := loweredMatrix_pair_bilinear G K hsym hG.det_pos.ne'
    (fun a => p ![a]) (fun a => q ![a])
  rw [hp,hq] at H
  exact H

 theorem scalarJet_covector_derivative (k : HermitianField M) (f : M.Carrier → ℝ)
    (c : M.Carrier) (z : ComplexVector n) (i : RIdx n) (u : Fin 1 → RIdx n) :
    covariantD k c (scalarJet k f c 1) z (Fin.cons i u) =
      Yau.Proofs.C05GradientFlowAux.realHessInChart k f c z i (u 0) := by
  have he : Fin.cons i u = ![i,u 0] := by
    funext j
    fin_cases j <;> simp [Fin.cons_one]
  change scalarJet k f c 2 z (Fin.cons i u) = _
  rw [he,scalarJet_two]

 theorem half_inverseEnergyHessianSquare_eq (k : HermitianField M) (f : M.Carrier → ℝ)
    (c : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget c) :
    (1/2 : ℝ)*inverseEnergyHessianSquare k f c z =
      hessianEnergy (realMetricFn k c z) (Matrix.of (realRicciCoeff k c z))
        (Matrix.of (Yau.Proofs.C05GradientFlowAux.realHessInChart k f c z)) := by
  let G := realMetricFn k c z
  let A := Matrix.of (realRicciCoeff k c z)
  let B := Matrix.of (Yau.Proofs.C05GradientFlowAux.realHessInChart k f c z)
  have hG : G.IsSymm := Yau.LeafProofs.L18Aux.realMetricFn_isSymm k c z
  have hdet : G.det ≠ 0 := (realMetricFn_posDef k c z hz).det_pos.ne'
  unfold hessianEnergy inverseEnergyHessianSquare
  change (1/2 : ℝ)*(∑ i, ∑ j, G⁻¹ i j*covTensorPair G (ricciInverseTensor k c z)
    (tensorConcatProduct
      (fun u => covariantD k c (scalarJet k f c 1) z (Fin.cons i u))
      (fun u => covariantD k c (scalarJet k f c 1) z (Fin.cons j u)))) =
    (1/2 : ℝ)*(G⁻¹*B*A⁻¹*Bᵀ).trace
  congr 1
  rw [hessianTrace_eq_sum G A B hG]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply congrArg (fun t : ℝ => G⁻¹ i j*t)
  change covTensorPair G (matrixCovTensor (loweredInverseMatrix G A)) _ = _
  simp_rw [scalarJet_covector_derivative k f c z]
  exact loweredInverseMatrix_pair_bilinear G A hG hdet (B i) (B j)

end Yau.Proofs.C05HessianEnergyAux
