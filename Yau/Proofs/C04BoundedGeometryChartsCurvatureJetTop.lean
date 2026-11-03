import Yau.Proofs.C04BoundedGeometryChartsCurvatureTrilinear
import Yau.Proofs.C04BoundedGeometryChartsJetBudgets
import Yau.Proofs.C04TrilinearJetTop

/-! In the actual curvature operator only two terms contain the highest coframe jet. -/
noncomputable section
open scoped Topology Manifold ContDiff
namespace Yau.Proofs.C04ChartsAux
open Yau Yau.LeafProofs.L23Aux Yau.Proofs.C04Aux.TrilinearJetTopAux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 5

def curvatureTopCoefficient (n : ℕ) (K : ℕ → ℝ) : ℝ :=
  2 * ‖curvatureContraction n‖ * curvatureFormModelBound n K 0 * 2

def curvatureLowerJetBudget (n : ℕ) (K : ℕ → ℝ) (m : ℕ) (L : ℝ) : ℝ :=
  ‖curvatureContraction n‖ * leibnizConstant m *
    (curvatureTowerBudget n K m * ((2 : ℝ)^m * tensorTowerModelBudget n m * L)^m) * L^2

theorem curvatureTopCoefficient_nonneg (K : ℕ → ℝ) (hK : ∀ j, 0 ≤ K j) :
    0 ≤ curvatureTopCoefficient n K := by
  unfold curvatureTopCoefficient
  positivity [curvatureFormModelBound_nonneg (n := n) K hK 0]

theorem curvatureLowerJetBudget_nonneg (K : ℕ → ℝ) (hK : ∀ j, 0 ≤ K j)
    (m : ℕ) {L : ℝ} (hL : 1 ≤ L) : 0 ≤ curvatureLowerJetBudget n K m L := by
  have hB := curvatureTowerBudget_one_le (n := n) K hK m
  have hD := tensorTowerModelBudget_one_le n m
  have hS := leibnizConstant_nonneg m
  unfold curvatureLowerJetBudget
  positivity

theorem radialCurvatureOperator_jet_top
    (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p)
    (hU : ∀ i j, (g.form p).toFun (U (stdVec i)) (U (stdVec j)) =
      (1 : Matrix (Fin n) (Fin n) ℂ) i j)
    (K : ℕ → ℝ) (hK : ∀ j, 0 ≤ K j) (m : ℕ) (hm : 1 ≤ m) (v : ComplexVector n)
    {L : ℝ} (hL : 1 ≤ L)
    (hcurv : ∀ j ≤ m, curvatureJetNorm g.form j (unitaryExponential g p U v) ≤ K j)
    (hA0 : ‖radialCoframe g p U v‖ ≤ 2)
    (hA : ∀ l < m, ‖iteratedFDeriv ℝ l (radialCoframe g p U) v‖ ≤ L)
    (hw : ∀ l < m, ‖iteratedFDeriv ℝ l (radialConnection g p U) v‖ ≤ L) :
    ‖iteratedFDeriv ℝ m (radialCurvatureOperator g p U) v‖ ≤
      curvatureTopCoefficient n K * ‖iteratedFDeriv ℝ m (radialCoframe g p U) v‖ +
        curvatureLowerJetBudget n K m L := by
  have hB := curvatureTowerBudget_one_le (n := n) K hK m
  have hD := tensorTowerModelBudget_one_le n m
  have hH : 1 ≤ (2 : ℝ)^m * tensorTowerModelBudget n m * L :=
    one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) hD) hL
  have ht := radialCurvatureForm_triangular_jets g p U m v
    (le_trans zero_le_one hB) hL (le_trans zero_le_one hD) hH le_rfl
    (fun j hj => (radialCurvatureForm_norm_le g p U hU j v (hK j) (hcurv j hj)).trans
      (curvatureFormModelBound_le_budget K hK hj))
    (fun j hj => tensorModelStepNorm_le_budget hj) hA hw
  have hfj : ∀ j ≤ m, ‖iteratedFDeriv ℝ j (radialCurvatureForm g p U 0) v‖ ≤
      curvatureTowerBudget n K m * ((2 : ℝ)^m * tensorTowerModelBudget n m * L)^m := by
    intro j hj
    exact (ht j 0 (by omega)).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hH hj) (le_trans zero_le_one hB))
  have hT0 : ‖radialCurvatureForm g p U 0 v‖ ≤ curvatureFormModelBound n K 0 :=
    radialCurvatureForm_norm_le g p U hU 0 v (hK 0) (hcurv 0 (by omega))
  have hh := trilinear_jet_bound_top_two (curvatureContraction n) hm
    ((radialCurvatureForm_smooth g p U 0).of_le (by simp))
    ((radialCoframe_smooth g p U).of_le (by simp)) v
    (mul_nonneg (le_trans zero_le_one hB) (pow_nonneg (le_trans zero_le_one hH) _))
    (le_trans zero_le_one hL) hT0 hA0 hfj hA
  have heq : (fun y => curvatureContraction n (radialCurvatureForm g p U 0 y)
      (radialCoframe g p U y) (radialCoframe g p U y)) = radialCurvatureOperator g p U :=
    funext (fun y => (radialCurvatureOperator_eq_contraction g p U y).symm)
  rw [heq] at hh
  exact hh

end Yau.Proofs.C04ChartsAux
