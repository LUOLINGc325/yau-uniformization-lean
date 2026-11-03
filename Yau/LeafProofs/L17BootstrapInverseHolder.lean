import Yau.LeafProofs.L17LocalHolderBanachAlgebra
import Yau.LeafProofs.L17BootstrapInverseHolderMatrix

open Set Metric
open scoped Topology Matrix.Norms.Frobenius ComplexOrder
noncomputable section
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17BootstrapInverseHolderAux

open Yau.LeafProofs.L17Aux Yau.LeafProofs.L17SchauderAux
open Yau.LeafProofs.L17LocalHolderBanachAlgebraAux

local instance bootstrapInverseHolder_matrixTopology (n : ℕ) :
    TopologicalSpace (Matrix (Fin n) (Fin n) ℂ) :=
  (Matrix.frobeniusNormedAddCommGroup :
    NormedAddCommGroup (Matrix (Fin n) (Fin n) ℂ)).toUniformSpace.toTopologicalSpace

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
  {P : UniformChartPartition g} {T gamma : ℝ}

theorem exists_inverse_holder_of_uniform_positive
    (H : LocalHolderBanach (Matrix (Fin n) (Fin n) ℂ) P T gamma)
    (lambda : ℝ) (hlambda : 0 < lambda)
    (hLower : ∀ q : LocalCylinder P T,
      (H q-(lambda : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosSemidef) :
    ∃ (K : LocalHolderBanach (Matrix (Fin n) (Fin n) ℂ) P T gamma) (B : ℝ),
      1 ≤ B ∧ (∀ q : LocalCylinder P T, K q=(H q)⁻¹) ∧
      H*K=1 ∧ K*H=1 ∧ ‖K‖ ≤ 2*(1+B+B^2*‖H.value‖) := by
  classical
  let F := Matrix (Fin n) (Fin n) ℂ
  have hUnit (q : LocalCylinder P T) : IsUnit (H q) :=
    (matrix_posDef_of_uniform_lower hlambda (hLower q)).isUnit
  have hHBound (q : LocalCylinder P T) : ‖H q‖ ≤ 1+‖H‖ := by
    have hEval := (localValue_norm_le F H.value q).trans
      (norm_value_le_half F P T gamma H)
    change ‖H q‖ ≤ (1/2 : ℝ)*‖H‖ at hEval
    linarith [norm_nonneg H]
  obtain ⟨B,hB,hBound⟩ := exists_uniform_inverse_norm_bound n lambda (1+‖H‖) hlambda
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  let f : LocalCylinder P T → F := fun q => (H q)⁻¹
  have hHContinuous : Continuous (fun q : LocalCylinder P T => H q) := H.value.val.1.continuous
  have hf : Continuous f := by
    apply continuous_iff_continuousAt.mpr
    intro q
    exact (matrix_inverse_continuousAt_of_isUnit (hUnit q)).comp hHContinuous.continuousAt
  have hSup (q : LocalCylinder P T) : ‖f q‖ ≤ B := hBound (H q) (hHBound q) (hLower q)
  have hDiff (i : L17HolderAux.ChartPairs P T) :
      ‖L17HolderAux.pairWeight P T gamma i •
        (f (localRight P T i)-f (localLeft P T i))‖ ≤ B^2*‖H.value‖ := by
    apply matrix_weighted_inverse_difference_norm_le
      (hUnit (localRight P T i)) (hUnit (localLeft P T i)) _ hB0
      (hSup (localRight P T i)) (hSup (localLeft P T i))
    have hd := localWeighted_difference_norm_le F H.value i
    change ‖L17HolderAux.pairWeight P T gamma i •
      (H (localRight P T i)-H (localLeft P T i))‖ ≤ ‖H.value‖ at hd
    simpa only [← neg_sub (H (localRight P T i)) (H (localLeft P T i)),smul_neg,norm_neg] using hd
  let raw := localOfBounds F P T gamma f hf B (B^2*‖H.value‖) hSup hDiff
  let K : LocalHolderBanach F P T gamma := ⟨raw⟩
  have hK (q : LocalCylinder P T) : K q=(H q)⁻¹ := rfl
  refine ⟨K,B,hB,hK,?_,?_,?_⟩
  · apply L17LocalHolderBanachAlgebraAux.ext
    intro q
    rw [mul_apply,one_apply,hK]
    exact (H q).mul_nonsing_inv ((H q).isUnit_iff_isUnit_det.mp (hUnit q))
  · apply L17LocalHolderBanachAlgebraAux.ext
    intro q
    rw [mul_apply,one_apply,hK]
    exact (H q).nonsing_inv_mul ((H q).isUnit_iff_isUnit_det.mp (hUnit q))
  · have hN : 0 ≤ B^2*‖H.value‖ := mul_nonneg (sq_nonneg B) (norm_nonneg _)
    have hRaw := localOfBounds_norm_le F P T gamma f hf B (B^2*‖H.value‖) hB0 hN hSup hDiff
    have hMax : max B (B^2*‖H.value‖) ≤ 1+B+B^2*‖H.value‖ := by
      apply max_le <;> linarith
    rw [norm_eq_twice]
    exact mul_le_mul_of_nonneg_left (hRaw.trans hMax) (by norm_num)

end Yau.LeafProofs.L17BootstrapInverseHolderAux
