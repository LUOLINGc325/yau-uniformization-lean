import Yau.Proofs.C05LoweredInverseDerivative
import Yau.LeafProofs.L23RicciBound

/-! The original scalar Harnack quadratic is a genuine metric tensor
pairing with the lowered inverse of the actual Ricci form. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder

namespace Yau.Proofs.C05Aux
open Yau Yau.LeafProofs.L23Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false

theorem matrixCovTensor_evaluation (B : Matrix (RIdx n) (RIdx n) ℝ) (v : RIdx n → ℝ) :
    tensorEvaluation (matrixCovTensor B) (fun _ : Fin 2 => v) = v ⬝ᵥ (B *ᵥ v) := by
  simp only [tensorEvaluation, tensorProduct, matrixCovTensor, sum_tensor_cons,
    Fin.prod_univ_succ, Fin.prod_univ_zero, Fin.cons_zero, Fin.cons_succ,
    mul_one, Fintype.sum_unique, dotProduct, Matrix.mulVec, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  have h1 : (1 : Fin 2) = (0 : Fin 1).succ := rfl
  simp only [h1, Fin.cons_succ, Fin.cons_zero]
  ring

theorem loweredInverseMatrix_pair (G A : Matrix (RIdx n) (RIdx n) ℝ)
    (hG : G.PosDef) (p : RIdx n → ℝ) :
    covTensorPair G (matrixCovTensor (loweredInverseMatrix G A))
        (tensorProduct (fun _ : Fin 2 => p)) = p ⬝ᵥ (A⁻¹ *ᵥ p) := by
  let v := G⁻¹ *ᵥ p
  have hHG : G⁻¹ * G = 1 := Matrix.nonsing_inv_mul G
    (isUnit_iff_ne_zero.mpr hG.det_pos.ne')
  have hGv : G *ᵥ v = p := by
    dsimp only [v]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv G
      (isUnit_iff_ne_zero.mpr hG.det_pos.ne'), Matrix.one_mulVec]
  have hh := tensorEvaluation_eq_contraction G G⁻¹ hHG
    (matrixCovTensor (loweredInverseMatrix G A)) (fun _ : Fin 2 => v)
  simp only [hGv] at hh
  change covTensorPair G (matrixCovTensor (loweredInverseMatrix G A))
    (tensorProduct (fun _ : Fin 2 => p)) = _ at hh
  rw [hh, matrixCovTensor_evaluation]
  apply loweredInverseMatrix_quadratic G A _ hG.det_pos.ne' p
  change Gᵀ = G
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hG.isHermitian.eq

def ricciInverseTensor (k : HermitianField M) (c : M.Carrier)
    (z : ComplexVector n) : CovTensor n 2 :=
  matrixCovTensor (loweredInverseMatrix (realMetricFn k c z)
    (Matrix.of (realRicciCoeff k c z)))

theorem realRicciDifferentialEnergy_eq_pair (k : HermitianField M)
    (f : M.Carrier → ℝ) (x : M.Carrier) :
    realRicciDifferentialEnergy k f x = (1 / 2 : ℝ) *
      covTensorPair (realMetricFn k x (chartPt x x))
        (ricciInverseTensor k x (chartPt x x))
        (tensorProduct (fun _ : Fin 2 => fun a => rDeriv (inChart x f) (chartPt x x) a)) := by
  unfold ricciInverseTensor
  rw [loweredInverseMatrix_pair (realMetricFn k x (chartPt x x))
    (Matrix.of (realRicciCoeff k x (chartPt x x)))
    (Yau.LeafProofs.L12Aux.realMetricFn_posDef k x _ (mem_extChartAt_target x))
    (fun a => rDeriv (inChart x f) (chartPt x x) a)]
  unfold realRicciDifferentialEnergy
  congr 1
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem scalar_differential_ricci_tensor_pair (k : HermitianField M) (hk : MetricSmooth k)
    (hK : KahlerClosed k) (f : M.Carrier → ℝ) (hf : SmoothFn f) (x : M.Carrier)
    (hA : (ricci k x).PosDef) :
    dualNormMat (ricci k x) (WithLp.toLp 2 (fun i =>
      wirt (fun z => Complex.ofReal (inChart x f z)) (chartPt x x) (stdVec i))) =
        (1 / 2 : ℝ) * covTensorPair (realMetricFn k x (chartPt x x))
          (ricciInverseTensor k x (chartPt x x))
          (tensorProduct (fun _ : Fin 2 => fun a =>
            rDeriv (inChart x f) (chartPt x x) a)) := by
  rw [scalar_differential_ricci_dual_eq k hk hK f hf x hA,
    realRicciDifferentialEnergy_eq_pair]

end Yau.Proofs.C05Aux
