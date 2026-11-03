import Yau.Proofs.V02DampedTrace

/-! A single damping parameter is chosen before all smooth vector traces
with the prescribed genuine L² and Fourier bounds. -/

open scoped Topology ContDiff

noncomputable section
namespace Yau.Blueprint.V02Proof
open Yau Yau.Blueprint

theorem exists_uniform_outerDamping_parameter
    {ι : Type*} [Fintype ι] {B η : ℝ} (hB : 0 ≤ B) (hη : 0 < η) :
    ∃ P : ℝ, 0 < P ∧ ∀ u : ℝ → ι → ℂ,
      (∀ i, ContDiff ℝ ∞ (fun θ => u θ i)) →
      (∀ i, Function.Periodic (fun θ => u θ i) (2 * Real.pi)) →
      circleAverage (fun θ => ∑ i, ‖u θ i‖ ^ 2) ≤ B →
      boundaryDSq u ≤ ENNReal.ofReal B →
      ContDiffOn ℂ ∞ (outerDamping P u) (Metric.closedBall (0 : ℂ) 1) ∧
      (outerDamping P u 0).im = 0 ∧ 0 < (outerDamping P u 0).re ∧
      (∀ z ∈ Metric.closedBall (0 : ℂ) 1, ‖outerDamping P u z‖ ≤ 1) ∧
      boundaryDSq (fun θ (_ : Unit) => outerDamping P u (circlePoint θ)) ≤ 1 ∧
      -Real.log (outerDamping P u 0).re ≤ η ∧
      circleAverage (fun θ => 1 - ‖outerDamping P u (circlePoint θ)‖ ^ 2) ≤ η ∧
      (∀ i θ, ‖outerDamping P u (circlePoint θ) * u θ i‖ ≤ Real.sqrt P / 2) ∧
      (∀ i, boundaryDSq (fun θ (_ : Unit) =>
        outerDamping P u (circlePoint θ) * u θ i) ≤ ENNReal.ofReal (20 * B)) := by
  let P : ℝ := 1 + 4 * B + 2 * B / η
  have hP : 0 < P := by dsimp [P]; positivity
  have hfour : 4 * B / P ≤ 1 := by
    apply (div_le_iff₀ hP).mpr
    dsimp [P]
    have ht : 0 ≤ 2 * B / η := by positivity
    linarith
  have htwo : 2 * B / P ≤ η := by
    apply (div_le_iff₀ hP).mpr
    have ht : 2 * B / η ≤ P := by dsimp [P]; linarith
    have hm := mul_le_mul_of_nonneg_right ht hη.le
    rw [div_mul_cancel₀ _ hη.ne'] at hm
    nlinarith
  refine ⟨P, hP, fun u hu hp hmean hD => ?_⟩
  have hDα : boundaryDSq (fun θ (_ : Unit) => outerDamping P u (circlePoint θ)) ≤ 1 := by
    calc
      _ ≤ ENNReal.ofReal (4 / P) * boundaryDSq u := outerDamping_boundaryDSq_le hP hu hp
      _ ≤ ENNReal.ofReal (4 / P) * ENNReal.ofReal B := by gcongr
      _ = ENNReal.ofReal (4 * B / P) := by rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; ring
      _ ≤ 1 := by simpa using ENNReal.ofReal_le_ofReal hfour
  have hcenter : -Real.log (outerDamping P u 0).re ≤ η := by
    apply (outerDamping_center_loss hP hu).trans
    have hm := div_le_div_of_nonneg_right hmean hP.le
    have hb : B / P ≤ 2 * B / P :=
      div_le_div_of_nonneg_right (by linarith) hP.le
    exact hm.trans (hb.trans htwo)
  have hloss : circleAverage (fun θ => 1 - ‖outerDamping P u (circlePoint θ)‖ ^ 2) ≤ η := by
    apply (outerDamping_boundary_loss hP hu hp).trans
    have hm : 2 * circleAverage (fun θ => ∑ i, ‖u θ i‖ ^ 2) / P ≤ 2 * B / P :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hmean (show 0 ≤ (2 : ℝ) by norm_num)) hP.le
    exact hm.trans htwo
  refine ⟨outerDamping_contDiffOn hP hu hp, (outerDamping_center_phase P u).1,
    (outerDamping_center_phase P u).2, outerDamping_norm_le_one hP hu hp,
    hDα, hcenter, hloss, outerDamping_mul_norm_le hP hu hp, fun i => ?_⟩
  calc
    _ ≤ ENNReal.ofReal 20 * boundaryDSq u := outerDamping_mul_boundaryDSq_le hP hu hp i
    _ ≤ ENNReal.ofReal 20 * ENNReal.ofReal B := by gcongr
    _ = _ := (ENNReal.ofReal_mul (by norm_num)).symm

end Yau.Blueprint.V02Proof
