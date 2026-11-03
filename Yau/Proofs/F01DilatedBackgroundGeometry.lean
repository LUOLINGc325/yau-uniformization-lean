import Yau.Proofs.F01BackgroundInitialHolder
import Yau.Proofs.F01ParabolicDilation
import Yau.Proofs.F01MatrixSandwichMono
import Yau.Proofs.F01MatrixSmooth

/-! The genuine dilated bounded-geometry background has the original
Frobenius smoothness, positivity and numerical matrix sandwich required by
the initial estimate, with one comparison number before all scales/centers. -/
noncomputable section
open Set Metric
open scoped ContDiff Matrix ComplexOrder Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n} {α : HermitianField M}

theorem dilated_background_smooth (A : BoundedChartFamily α) (a : M.Carrier)
    {ρ : ℝ} (hρ : 0 < ρ) (hρr : ρ ≤ A.radius) :
    ContDiffOn ℝ ∞ (fun z => pullbackMatrix α (A.chart a) (ρ • z)) (ball (0 : Space n) 1) := by
  apply matrix_contDiffOn_of_entries
  intro i j
  have hs : ContDiffOn ℝ ∞ (fun z : Space n => ρ • z) (ball 0 1) := by fun_prop
  exact (A.coefficient_smooth a i j).comp hs
    (fun z hz => spatialDilation_mem_ball hρ hρr hz)

theorem dilated_background_posDef (A : BoundedChartFamily α) (a : M.Carrier)
    {ρ : ℝ} (hρ : 0 < ρ) (hρr : ρ ≤ A.radius) {z : Space n} (hz : z ∈ ball 0 1) :
    (pullbackMatrix α (A.chart a) (ρ • z)).PosDef :=
  pullbackMatrix_posDef α (A.chart a) (A.differentiable a) (A.inverse_differentiable a)
    (A.closedBall_source a (ball_subset_closedBall (spatialDilation_mem_ball hρ hρr hz)))

theorem dilated_background_uniform_sandwich (A : BoundedChartFamily α) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ A.radius → ∀ a : M.Carrier,
      ∀ z ∈ ball (0 : Space n) 1,
        (pullbackMatrix α (A.chart a) (ρ • z) - ((D⁻¹ : ℝ) : ℂ) • 1).PosSemidef ∧
        ((D : ℂ) • 1 - pullbackMatrix α (A.chart a) (ρ • z)).PosSemidef := by
  let D := max 1 (A.bound 0)
  have hD : 1 ≤ D := le_max_left _ _
  refine ⟨D, hD, ?_⟩
  intro ρ hρ hρr a z hz
  apply matrix_sandwich_mono (A.bound_pos 0) (zero_lt_one.trans_le hD) (le_max_right _ _)
  simpa only [Complex.ofReal_inv] using A.comparison a (ρ • z) (spatialDilation_mem_ball hρ hρr hz)

end Yau.NodeProofs.F01Aux
