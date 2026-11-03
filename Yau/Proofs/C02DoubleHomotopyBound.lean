import Yau.Proofs.C02RadialHomotopy

/-! Two actual radial homotopies gain a quadratic factor in the distance
from the origin. Only the curvature bound on the preceding radial segment
is used. -/

noncomputable section
open Set
open scoped ContDiff
namespace Yau.Blueprint.C02Proof
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

local instance double_end_group : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
local instance double_end_space : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
local instance double_one_group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance double_one_space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance double_two_group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance double_two_space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] E) := inferInstance

theorem double_radial_homotopy_bound
    (A : E → E →L[ℝ] E →L[ℝ] E) (B : E → E →L[ℝ] E)
    (F : E → E →L[ℝ] E →L[ℝ] E →L[ℝ] E)
    (hA : ∀ y, A y = radialHomotopy F y)
    (hB : ∀ y, B y = ContinuousLinearMap.id ℝ E + radialHomotopy (fun z => (A z).flip) y)
    (x : E) {L : ℝ} (hL : 0 ≤ L)
    (hF : ∀ t ∈ Icc (0 : ℝ) 1, ‖F (t • x)‖ ≤ L) :
    ‖B x - ContinuousLinearMap.id ℝ E‖ ≤ ‖x‖ ^ 2 / 4 * L := by
  have hAx : ∀ s ∈ Icc (0 : ℝ) 1, ‖A (s • x)‖ ≤ ‖x‖ / 2 * L := by
    intro s hs
    rw [hA]
    have hf : ∀ t ∈ Icc (0 : ℝ) 1, ‖F (t • (s • x))‖ ≤ L := by
      intro t ht
      rw [smul_smul]
      exact hF (t * s) ⟨mul_nonneg ht.1 hs.1,
        (mul_le_of_le_one_left hs.1 ht.2).trans hs.2⟩
    have hb := norm_radialHomotopy_le F (s • x) L hL hf
    have hnx : ‖s • x‖ ≤ ‖x‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1]
      exact mul_le_of_le_one_left (norm_nonneg x) hs.2
    exact hb.trans (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hnx (by norm_num)) hL)
  have hAf : ∀ s ∈ Icc (0 : ℝ) 1, ‖(A (s • x)).flip‖ ≤ ‖x‖ / 2 * L := by
    intro s hs
    rw [ContinuousLinearMap.opNorm_flip]
    exact hAx s hs
  rw [hB, add_sub_cancel_left]
  have hb := norm_radialHomotopy_le (fun y => (A y).flip) x (‖x‖ / 2 * L) (by positivity) hAf
  calc
    _ ≤ ‖x‖ / 2 * (‖x‖ / 2 * L) := hb
    _ = _ := by ring

end Yau.Blueprint.C02Proof
