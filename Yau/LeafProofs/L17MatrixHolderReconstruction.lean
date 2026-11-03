import Yau.LeafProofs.L17PotentialLeviMap
import Mathlib.Data.Matrix.Basis

open Set Metric
open scoped Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17Aux
open L17HolderAux L17SchauderAux L17LocalHolderAlgebraAux
local instance (n : ℕ) : TopologicalSpace (Matrix (Fin n) (Fin n) ℂ) := leviMatrixTopology n

theorem frobenius_single_norm {n : ℕ} (i j : Fin n) (c : ℂ) :
    ‖Matrix.single i j c‖ = ‖c‖ := by
  calc
    _ = (‖c‖^2)^(1/2 : ℝ) := by
      simp [Matrix.frobenius_norm_def,Matrix.single,ite_and,apply_ite]
    _ = ‖c‖ := by rw [← Real.sqrt_eq_rpow,Real.sqrt_sq_eq_abs,abs_norm]

def matrixSingleCLM {n : ℕ} (i j : Fin n) : ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
  (Matrix.singleLinearMap ℝ i j).mkContinuous 1 (fun c => by
    simpa only [Matrix.singleLinearMap_apply,one_mul] using (frobenius_single_norm i j c).le)

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
variable {P : UniformChartPartition g} {T γ : ℝ}

def matrixHolderOfEntries (u : Fin n → Fin n → LocalHolderSpace ℂ P T γ) :
    LocalHolderSpace (Matrix (Fin n) (Fin n) ℂ) P T γ :=
  ∑ i, ∑ j, localMapCLM (matrixSingleCLM i j) (u i j)

theorem matrixHolderOfEntries_value (u : Fin n → Fin n → LocalHolderSpace ℂ P T γ)
    (q : LocalCylinder P T) :
    localFun _ (matrixHolderOfEntries u) q = fun i j => localFun ℂ (u i j) q := by
  change (localEvalCLM _ P T γ q) (∑ i, ∑ j, localMapCLM (matrixSingleCLM i j) (u i j)) = _
  simp only [map_sum]
  change (∑ i, ∑ j, Matrix.single i j (localFun ℂ (u i j) q)) = _
  exact Matrix.sum_sum_single _

theorem matrixSingleCLM_opNorm_le_one {n : ℕ} (i j : Fin n) : ‖matrixSingleCLM i j‖ ≤ 1 :=
  (matrixSingleCLM i j).opNorm_le_bound zero_le_one (fun c => by
    simpa only [matrixSingleCLM,LinearMap.mkContinuous_apply,Matrix.singleLinearMap_apply,one_mul]
      using (frobenius_single_norm i j c).le)

theorem matrixHolderOfEntries_norm_le (u : Fin n → Fin n → LocalHolderSpace ℂ P T γ) :
    ‖matrixHolderOfEntries u‖ ≤ ∑ i, ∑ j, ‖u i j‖ := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j hj
  exact (localMapElement_norm_le (matrixSingleCLM i j) (u i j)).trans
    ((mul_le_mul_of_nonneg_right (matrixSingleCLM_opNorm_le_one i j) (norm_nonneg _)).trans_eq (one_mul _))

end Yau.LeafProofs.L17Aux
