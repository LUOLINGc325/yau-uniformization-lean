import Yau.LeafProofs.L17MatrixHolderReconstruction
import Yau.LeafProofs.L17SpatialCoefficientHolder
import Yau.LeafProofs.L17InverseMatrixEntryBounds
import Yau.LeafProofs.L17LocalHolderBanachAlgebra

open Set Metric
open scoped Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17Aux
open L17HolderAux L17SchauderAux L17LocalHolderAlgebraAux L17LocalHolderBanachAlgebraAux
local instance (n : ℕ) : TopologicalSpace (Matrix (Fin n) (Fin n) ℂ) := leviMatrixTopology n
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
variable (P : UniformChartPartition g) {T γ : ℝ}

def inverseMatrixEntryHolder (hTime : T ≤ P.radius^2) (hγ : γ ≤ 1) (hr : P.radius ≤ 1)
    (i j : Fin n) : LocalHolderSpace ℂ P T γ :=
  spatialCoefficientHolder P hTime hγ hr
    (zero_le_one.trans (inverseMatrixEntryBudget_ge_one P.charts i j))
    (inverseMatrixEntry P.charts i j)
    (fun p => (inverseMatrixEntry_smooth P.charts i j p).continuousOn.mono (ball_subset_ball P.radius_lt.le))
    (fun p _ hz => (inverseMatrixEntry_bounds P.charts i j p ((ball_subset_ball P.radius_lt.le) hz)).1)
    (fun p _ hz _ hw => inverseMatrixEntry_lipschitz P.charts i j p
      ((ball_subset_ball P.radius_lt.le) hz) ((ball_subset_ball P.radius_lt.le) hw))

theorem inverseMatrixEntryHolder_norm_le (hTime : T ≤ P.radius^2) (hγ : γ ≤ 1) (hr : P.radius ≤ 1)
    (i j : Fin n) :
    ‖inverseMatrixEntryHolder P hTime hγ hr i j‖ ≤
      inverseMatrixEntryBudget P.charts i j*(1+(3 : ℝ)^(1-γ)) :=
  spatialCoefficientHolder_norm_le P hTime hγ hr _ _ _ _ _

def inverseMatrixHolder (hTime : T ≤ P.radius^2) (hγ : γ ≤ 1) (hr : P.radius ≤ 1) :
    LocalHolderSpace (Matrix (Fin n) (Fin n) ℂ) P T γ :=
  matrixHolderOfEntries (inverseMatrixEntryHolder P hTime hγ hr)

theorem inverseMatrixHolder_value (hTime : T ≤ P.radius^2) (hγ : γ ≤ 1) (hr : P.radius ≤ 1)
    (q : LocalCylinder P T) :
    localFun _ (inverseMatrixHolder P hTime hγ hr) q =
      (pullbackMatrix g (P.charts.chart q.1) q.2.1)⁻¹ :=
  matrixHolderOfEntries_value _ q

def inverseMatrixHolderBudget (A : BoundedChartFamily g) (γ : ℝ) : ℝ :=
  1+(∑ i, ∑ j, inverseMatrixEntryBudget A i j)*(1+(3 : ℝ)^(1-γ))

theorem inverseMatrixHolderBudget_ge_one (A : BoundedChartFamily g) (γ : ℝ) :
    1 ≤ inverseMatrixHolderBudget A γ := by
  apply le_add_of_nonneg_right
  apply mul_nonneg
  · exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg
      (fun j _ => zero_le_one.trans (inverseMatrixEntryBudget_ge_one A i j)))
  · positivity

theorem inverseMatrixHolder_norm_le (hTime : T ≤ P.radius^2) (hγ : γ ≤ 1) (hr : P.radius ≤ 1) :
    ‖inverseMatrixHolder P hTime hγ hr‖ ≤ inverseMatrixHolderBudget P.charts γ := by
  apply (matrixHolderOfEntries_norm_le _).trans
  apply (Finset.sum_le_sum (fun i _ => Finset.sum_le_sum
    (fun j _ => inverseMatrixEntryHolder_norm_le P hTime hγ hr i j))).trans
  simp only [← Finset.sum_mul]
  exact le_add_of_nonneg_left zero_le_one

def inverseMatrixBanach (hTime : T ≤ P.radius^2) (hγ : γ ≤ 1) (hr : P.radius ≤ 1) :
    LocalHolderBanach (Matrix (Fin n) (Fin n) ℂ) P T γ :=
  ⟨inverseMatrixHolder P hTime hγ hr⟩

theorem inverseMatrixBanach_value (hTime : T ≤ P.radius^2) (hγ : γ ≤ 1) (hr : P.radius ≤ 1)
    (q : LocalCylinder P T) :
    inverseMatrixBanach P hTime hγ hr q = (pullbackMatrix g (P.charts.chart q.1) q.2.1)⁻¹ :=
  inverseMatrixHolder_value P hTime hγ hr q

theorem inverseMatrixBanach_norm_le (hTime : T ≤ P.radius^2) (hγ : γ ≤ 1) (hr : P.radius ≤ 1) :
    ‖inverseMatrixBanach P hTime hγ hr‖ ≤ 2*inverseMatrixHolderBudget P.charts γ := by
  rw [norm_eq_twice]
  exact mul_le_mul_of_nonneg_left (inverseMatrixHolder_norm_le P hTime hγ hr) (by norm_num)

end Yau.LeafProofs.L17Aux
