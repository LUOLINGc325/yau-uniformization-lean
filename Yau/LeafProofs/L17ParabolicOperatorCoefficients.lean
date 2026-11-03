import Yau.LeafProofs.L17ParabolicOperatorContraction
import Yau.LeafProofs.L17HolderEmbedding
import Mathlib.Analysis.Calculus.MeanValue

open Set Metric
open scoped Topology ContDiff Matrix.Norms.Elementwise
noncomputable section
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17ParabolicOperatorAux
open Yau.LeafProofs.L17Aux Yau.LeafProofs.L17HolderAux Yau.LeafProofs.L17SchauderAux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}


def chartCoefficient (A : BoundedChartFamily g) (p : M.Carrier) (z : ComplexVector n) :
    Matrix (RIdx n) (RIdx n) ℝ := scalarSymbol (pullbackMatrix g (A.chart p) z)

theorem chartCoefficient_eq_linear (A : BoundedChartFamily g) (p : M.Carrier) (z : ComplexVector n) :
    chartCoefficient A p z = ((1/4 : ℝ) • (scalarRealificationCLM (n := n)))
      (pullbackMatrix g (A.chart p) z)⁻¹ := rfl

theorem chartCoefficient_smooth (A : BoundedChartFamily g) (p : M.Carrier) :
    ContDiffOn ℝ ∞ (chartCoefficient A p) (ball 0 A.radius) :=
  (((1/4 : ℝ) • (scalarRealificationCLM (n := n))).contDiff.comp_contDiffOn (A.inverseMatrix_smooth p))

theorem chartCoefficient_uniformJetBounds (A : BoundedChartFamily g) (k : ℕ) :
    UniformJetBounds k (chartCoefficient A) (fun _ => ball 0 A.radius) :=
  (A.inverseMatrix_uniformJetBounds k).comp_clm (fun _ => isOpen_ball) A.inverseMatrix_smooth
    ((1/4 : ℝ) • (scalarRealificationCLM (n := n)))

theorem exists_coefficient_budget (A : BoundedChartFamily g) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ p z, z ∈ ball (0 : ComplexVector n) A.radius →
      ‖chartCoefficient A p z‖ ≤ C ∧ ‖iteratedFDeriv ℝ 1 (chartCoefficient A p) z‖ ≤ C := by
  obtain ⟨C,hC,hb⟩ := chartCoefficient_uniformJetBounds A 1
  refine ⟨C,hC,?_⟩
  intro p z hz
  exact ⟨by simpa only [norm_iteratedFDeriv_zero] using hb p z hz 0 (by omega),
    hb p z hz 1 (by omega)⟩

def coefficientBudget (A : BoundedChartFamily g) : ℝ := Classical.choose (exists_coefficient_budget A)

theorem coefficientBudget_ge_one (A : BoundedChartFamily g) : 1 ≤ coefficientBudget A :=
  (Classical.choose_spec (exists_coefficient_budget A)).1

theorem chartCoefficient_bounds (A : BoundedChartFamily g) (p : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ ball (0 : ComplexVector n) A.radius) :
    ‖chartCoefficient A p z‖ ≤ coefficientBudget A ∧
      ‖iteratedFDeriv ℝ 1 (chartCoefficient A p) z‖ ≤ coefficientBudget A :=
  (Classical.choose_spec (exists_coefficient_budget A)).2 p z hz

theorem chartCoefficient_lipschitz (A : BoundedChartFamily g) (p : M.Carrier)
    {z w : ComplexVector n} (hz : z ∈ ball (0 : ComplexVector n) A.radius)
    (hw : w ∈ ball (0 : ComplexVector n) A.radius) :
    ‖chartCoefficient A p z-chartCoefficient A p w‖ ≤ coefficientBudget A*‖z-w‖ :=
  Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun y hy => ((chartCoefficient_smooth A p).contDiffAt (isOpen_ball.mem_nhds hy)).differentiableAt (by simp))
    (fun y hy => by simpa only [norm_iteratedFDeriv_one] using (chartCoefficient_bounds A p hy).2) (convex_ball _ _) hw hz

theorem weighted_chartCoefficient_difference (P : UniformChartPartition g)
    {T gamma : ℝ} (hT : T ≤ P.radius^2) (hgamma : gamma ≤ 1) (hr : P.radius ≤ 1)
    (i : ChartPairs P T) :
    ‖pairWeight P T gamma i • (chartCoefficient P.charts i.1 i.2.val.2.1-
      chartCoefficient P.charts i.1 i.2.val.1.1)‖ ≤ coefficientBudget P.charts*(3 : ℝ)^(1-gamma) := by
  let d := parabolicDistance i.2.val.1 i.2.val.2
  have hd : 0 < d := parabolicDistance_pos_of_ne i.2.property
  have hC : 0 ≤ coefficientBudget P.charts := zero_le_one.trans (coefficientBudget_ge_one _)
  have hz : (i.2.val.2.1 : ComplexVector n) ∈ ball 0 P.charts.radius :=
    (ball_subset_ball P.radius_lt.le) i.2.val.2.1.property
  have hw : (i.2.val.1.1 : ComplexVector n) ∈ ball 0 P.charts.radius :=
    (ball_subset_ball P.radius_lt.le) i.2.val.1.1.property
  have hdiff : ‖chartCoefficient P.charts i.1 i.2.val.2.1-chartCoefficient P.charts i.1 i.2.val.1.1‖ ≤
      coefficientBudget P.charts*d :=
    (chartCoefficient_lipschitz P.charts i.1 hz hw).trans
      (mul_le_mul_of_nonneg_left (by
        dsimp only [d,parabolicDistance]
        rw [norm_sub_rev]
        exact le_add_of_nonneg_right (Real.sqrt_nonneg _)) hC)
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (pairWeight_pos P T gamma i)]
  calc
    _ ≤ ((3 : ℝ)^(1-gamma)*pairWeight P T 1 i)*(coefficientBudget P.charts*d) :=
      mul_le_mul (pairWeight_weaken_le P hT hgamma i) hdiff (norm_nonneg _)
        (mul_nonneg (Real.rpow_pos_of_pos (by norm_num) _).le (pairWeight_pos P T 1 i).le)
    _ = coefficientBudget P.charts*(3 : ℝ)^(1-gamma)*P.radius := by
      change ((3 : ℝ)^(1-gamma)*(P.radius^1/d^1))*(coefficientBudget P.charts*d) = _
      rw [Real.rpow_one,Real.rpow_one]
      field_simp [hd.ne']
    _ ≤ _ := (mul_le_mul_of_nonneg_left hr (mul_nonneg hC (Real.rpow_pos_of_pos (by norm_num) _).le)).trans_eq (mul_one _)

end Yau.LeafProofs.L17ParabolicOperatorAux
