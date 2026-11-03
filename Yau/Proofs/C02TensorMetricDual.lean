import Yau.Proofs.C02TensorCurvatureNorm

/-! The metric-dual curvature action is a fixed continuous linear
contraction of a four-covariant tensor, of norm at most one. -/

noncomputable section
open scoped InnerProductSpace
namespace Yau.Blueprint.C02Proof
variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
local instance dual_end_group : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
local instance dual_end_space : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
local instance dual_one_group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance dual_one_space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance dual_two_group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance dual_two_space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] E) := inferInstance

abbrev HomogeneousTensor (r : ℕ) := ContinuousMultilinearMap ℝ (fun _ : Fin r => E) ℝ

def tensorMetricDualOne : HomogeneousTensor E 1 →L[ℝ] E :=
  (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (continuousMultilinearCurryFin1 ℝ E ℝ).toContinuousLinearEquiv.toContinuousLinearMap

def tensorMetricDualTwo : HomogeneousTensor E 2 →L[ℝ] E →L[ℝ] E :=
  (ContinuousLinearMap.compL ℝ E (HomogeneousTensor E 1) E (tensorMetricDualOne E)).comp
    (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 2 => E) ℝ).toContinuousLinearEquiv.toContinuousLinearMap

def tensorMetricDualThree : HomogeneousTensor E 3 →L[ℝ] E →L[ℝ] E →L[ℝ] E :=
  (ContinuousLinearMap.compL ℝ E (HomogeneousTensor E 2) (E →L[ℝ] E) (tensorMetricDualTwo E)).comp
    (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 3 => E) ℝ).toContinuousLinearEquiv.toContinuousLinearMap

def tensorMetricDualFour : HomogeneousTensor E 4 →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] E :=
  (ContinuousLinearMap.compL ℝ E (HomogeneousTensor E 3) (E →L[ℝ] E →L[ℝ] E)
    (tensorMetricDualThree E)).comp
    (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 4 => E) ℝ).toContinuousLinearEquiv.toContinuousLinearMap

theorem tensorMetricDualOne_pairing (T : HomogeneousTensor E 1) (z : E) :
    ⟪tensorMetricDualOne E T, z⟫_ℝ = T ![z] := by
  rw [tensorMetricDualOne, ContinuousLinearMap.comp_apply]
  change ⟪(InnerProductSpace.toDual ℝ E).symm (continuousMultilinearCurryFin1 ℝ E ℝ T), z⟫_ℝ = _
  rw [InnerProductSpace.toDual_symm_apply, continuousMultilinearCurryFin1_apply]
  congr 1
  funext i
  fin_cases i
  rfl

theorem tensorMetricDualFour_pairing (T : HomogeneousTensor E 4) (u v w z : E) :
    ⟪tensorMetricDualFour E T u v w, z⟫_ℝ = T ![u, v, w, z] := by
  change ⟪tensorMetricDualOne E (((T.curryLeft u).curryLeft v).curryLeft w), z⟫_ℝ = _
  rw [tensorMetricDualOne_pairing]
  rfl

theorem tensorMetricDualFour_norm_le_one : ‖tensorMetricDualFour E‖ ≤ 1 := by
  apply (tensorMetricDualFour E).opNorm_le_bound (by norm_num)
  intro T
  have h := curvature_action_norm_le (tensorMetricDualFour E T) T (ContinuousLinearMap.id ℝ E)
    (by simpa only [ContinuousLinearMap.id_apply] using tensorMetricDualFour_pairing E T)
  have hI : ‖ContinuousLinearMap.id ℝ E‖ ^ 2 ≤ 1 := by
    have hi := ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := E)
    nlinarith [norm_nonneg (ContinuousLinearMap.id ℝ E)]
  simpa only [one_mul, mul_one] using h.trans (mul_le_mul_of_nonneg_left hI (norm_nonneg T))

end Yau.Blueprint.C02Proof
