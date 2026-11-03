import Yau.LeafProofs.L17MetricJetMaps
import Mathlib.Analysis.Calculus.MeanValue

open Set Metric
open scoped ContDiff Matrix.Norms.Elementwise
noncomputable section
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

def inverseMatrixEntry (A : BoundedChartFamily g) (i j : Fin n)
    (p : M.Carrier) (z : ComplexVector n) : ℂ :=
  (pullbackMatrix g (A.chart p) z)⁻¹ i j

theorem inverseMatrixEntry_smooth (A : BoundedChartFamily g) (i j : Fin n) (p : M.Carrier) :
    ContDiffOn ℝ ∞ (inverseMatrixEntry A i j p) (ball 0 A.radius) :=
  (matrixEntryCLM i j : Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℂ).contDiff.comp_contDiffOn (A.inverseMatrix_smooth p)

theorem inverseMatrixEntry_uniformJetBounds (A : BoundedChartFamily g) (i j : Fin n) (k : ℕ) :
    UniformJetBounds k (inverseMatrixEntry A i j) (fun _ => ball 0 A.radius) :=
  (A.inverseMatrix_uniformJetBounds k).comp_clm (fun _ => isOpen_ball) A.inverseMatrix_smooth
    (matrixEntryCLM i j)

theorem exists_inverseMatrixEntry_budget (A : BoundedChartFamily g) (i j : Fin n) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ p z, z ∈ ball (0 : ComplexVector n) A.radius →
      ‖inverseMatrixEntry A i j p z‖ ≤ C ∧
      ‖fderiv ℝ (inverseMatrixEntry A i j p) z‖ ≤ C := by
  obtain ⟨C,hC,hb⟩ := inverseMatrixEntry_uniformJetBounds A i j 1
  refine ⟨C,hC,?_⟩
  intro p z hz
  exact ⟨by simpa only [norm_iteratedFDeriv_zero] using hb p z hz 0 (by omega),
    by simpa only [norm_iteratedFDeriv_one] using hb p z hz 1 (by omega)⟩

def inverseMatrixEntryBudget (A : BoundedChartFamily g) (i j : Fin n) : ℝ :=
  Classical.choose (exists_inverseMatrixEntry_budget A i j)

theorem inverseMatrixEntryBudget_ge_one (A : BoundedChartFamily g) (i j : Fin n) :
    1 ≤ inverseMatrixEntryBudget A i j :=
  (Classical.choose_spec (exists_inverseMatrixEntry_budget A i j)).1

theorem inverseMatrixEntry_bounds (A : BoundedChartFamily g) (i j : Fin n) (p : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ ball (0 : ComplexVector n) A.radius) :
    ‖inverseMatrixEntry A i j p z‖ ≤ inverseMatrixEntryBudget A i j ∧
    ‖fderiv ℝ (inverseMatrixEntry A i j p) z‖ ≤ inverseMatrixEntryBudget A i j :=
  (Classical.choose_spec (exists_inverseMatrixEntry_budget A i j)).2 p z hz

theorem inverseMatrixEntry_lipschitz (A : BoundedChartFamily g) (i j : Fin n) (p : M.Carrier)
    {z w : ComplexVector n} (hz : z ∈ ball (0 : ComplexVector n) A.radius)
    (hw : w ∈ ball (0 : ComplexVector n) A.radius) :
    ‖inverseMatrixEntry A i j p z-inverseMatrixEntry A i j p w‖ ≤
      inverseMatrixEntryBudget A i j*‖z-w‖ :=
  Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun y hy => ((inverseMatrixEntry_smooth A i j p).contDiffAt
      (isOpen_ball.mem_nhds hy)).differentiableAt (by simp))
    (fun y hy => (inverseMatrixEntry_bounds A i j p hy).2) (convex_ball _ _) hw hz

end Yau.LeafProofs.L17Aux
