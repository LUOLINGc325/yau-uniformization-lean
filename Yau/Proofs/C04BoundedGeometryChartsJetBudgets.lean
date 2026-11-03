import Yau.Proofs.C04BoundedGeometryChartsTriangularJets

/-! Uniform numerical budgets for the intrinsic curvature tower. -/
noncomputable section
open scoped Topology Manifold ContDiff
namespace Yau.Proofs.C04ChartsAux
open Yau Yau.LeafProofs.L23Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 5

def curvatureFormModelBound (n : ℕ) (K : ℕ → ℝ) (j : ℕ) : ℝ :=
  ‖tensorEvalCLMMap (n := n) (r := 4 + j)‖ * (K j * Real.sqrt 2 ^ (4 + j))

def curvatureTowerBudget (n : ℕ) (K : ℕ → ℝ) (m : ℕ) : ℝ :=
  1 + ∑ j ∈ Finset.range (m + 1), curvatureFormModelBound n K j

def tensorTowerModelBudget (n m : ℕ) : ℝ :=
  1 + ∑ j ∈ Finset.range (m + 1), tensorModelStepNorm n j

theorem curvatureFormModelBound_nonneg (K : ℕ → ℝ) (hK : ∀ j, 0 ≤ K j) (j : ℕ) :
    0 ≤ curvatureFormModelBound n K j := by
  unfold curvatureFormModelBound
  exact mul_nonneg (norm_nonneg _) (mul_nonneg (hK j) (pow_nonneg (Real.sqrt_nonneg 2) _))

theorem curvatureTowerBudget_one_le (K : ℕ → ℝ) (hK : ∀ j, 0 ≤ K j) (m : ℕ) :
    1 ≤ curvatureTowerBudget n K m := by
  unfold curvatureTowerBudget
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun j _ => curvatureFormModelBound_nonneg K hK j)

theorem curvatureFormModelBound_le_budget (K : ℕ → ℝ) (hK : ∀ j, 0 ≤ K j)
    {j m : ℕ} (hjm : j ≤ m) : curvatureFormModelBound n K j ≤ curvatureTowerBudget n K m := by
  have H := Finset.single_le_sum (f := curvatureFormModelBound n K)
    (fun a _ => curvatureFormModelBound_nonneg K hK a)
    (show j ∈ Finset.range (m + 1) from Finset.mem_range.mpr (by omega))
  exact H.trans (le_add_of_nonneg_left (by norm_num))

theorem tensorTowerModelBudget_one_le (n m : ℕ) : 1 ≤ tensorTowerModelBudget n m := by
  unfold tensorTowerModelBudget
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun j _ => tensorModelStepNorm_nonneg n j)

theorem tensorModelStepNorm_le_budget {j m : ℕ} (hjm : j ≤ m) :
    tensorModelStepNorm n j ≤ tensorTowerModelBudget n m := by
  have H := Finset.single_le_sum (f := tensorModelStepNorm n)
    (fun a _ => tensorModelStepNorm_nonneg n a)
    (show j ∈ Finset.range (m + 1) from Finset.mem_range.mpr (by omega))
  exact H.trans (le_add_of_nonneg_left (by norm_num))

theorem radialCurvatureForm_triangular_bound
    (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p)
    (hU : ∀ i j, (g.form p).toFun (U (stdVec i)) (U (stdVec j)) =
      (1 : Matrix (Fin n) (Fin n) ℂ) i j)
    (K : ℕ → ℝ) (hK : ∀ j, 0 ≤ K j) (m : ℕ) (v : ComplexVector n)
    {L : ℝ} (hL : 1 ≤ L)
    (hcurv : ∀ j ≤ m, curvatureJetNorm g.form j (unitaryExponential g p U v) ≤ K j)
    (hA : ∀ l < m, ‖iteratedFDeriv ℝ l (radialCoframe g p U) v‖ ≤ L)
    (hw : ∀ l < m, ‖iteratedFDeriv ℝ l (radialConnection g p U) v‖ ≤ L) :
    ‖iteratedFDeriv ℝ m (radialCurvatureForm g p U 0) v‖ ≤
      curvatureTowerBudget n K m * ((2 : ℝ)^m * tensorTowerModelBudget n m * L)^m := by
  have hB := curvatureTowerBudget_one_le (n := n) K hK m
  have hD := tensorTowerModelBudget_one_le n m
  have hH : 1 ≤ (2 : ℝ)^m * tensorTowerModelBudget n m * L :=
    by
      have hp : (1 : ℝ) ≤ 2 ^ m := one_le_pow₀ (by norm_num)
      nlinarith [mul_nonneg (sub_nonneg.mpr hp) (sub_nonneg.mpr hD),
        mul_nonneg (sub_nonneg.mpr hL) (sub_nonneg.mpr (show 1 ≤ 2 ^ m * tensorTowerModelBudget n m by nlinarith [mul_nonneg (sub_nonneg.mpr hp) (sub_nonneg.mpr hD)]))]
  apply radialCurvatureForm_triangular_jets g p U m v
    (le_trans zero_le_one hB) hL (le_trans zero_le_one hD) hH le_rfl _ _ hA hw m 0 (by omega)
  · intro j hj
    exact (radialCurvatureForm_norm_le g p U hU j v (hK j) (hcurv j hj)).trans
      (curvatureFormModelBound_le_budget K hK hj)
  · intro j hj
    exact tensorModelStepNorm_le_budget hj

end Yau.Proofs.C04ChartsAux
