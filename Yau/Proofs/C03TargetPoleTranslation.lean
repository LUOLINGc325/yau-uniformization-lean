import Yau.Proofs.C03TargetPoleLevi

/-! Translation preserves the same quantitative pole constant and exact local form. -/
noncomputable section
open scoped Topology ContDiff
open Set Filter Metric
namespace Yau.Proofs.C03Aux.TargetPole
open Yau Yau.NodeProofs.P03Aux Yau.LeafProofs.L22Aux
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}
local instance : ContinuousSMul ℂ (ComplexVector n) where
  continuous_smul := by
    change Continuous (fun p : ℂ × ComplexVector n =>
      WithLp.toLp 2 (fun i => p.1 * p.2 i))
    exact (PiLp.continuous_toLp 2 (fun _ : Fin n => ℂ)).comp
      (continuous_pi fun i => continuous_fst.mul
        ((EuclideanSpace.proj i : ComplexVector n →L[ℂ] ℂ).continuous.comp continuous_snd))

def translatedPole (delta : ℝ) (hdelta : 0 < delta) (m j : ℕ)
    (a w : ComplexVector n) : ℝ := pole delta hdelta m j (w - a)

theorem translatedPole_contDiff (delta : ℝ) (hdelta : 0 < delta) (m j : ℕ)
    (a : ComplexVector n) : ContDiff ℝ ∞ (translatedPole delta hdelta m j a) :=
  (pole_contDiff delta hdelta m j).comp (contDiff_id.sub contDiff_const)

theorem translatedPole_tsupport_subset (delta : ℝ) (hdelta : 0 < delta) (m j : ℕ)
    (a : ComplexVector n) :
    tsupport (translatedPole delta hdelta m j a) ⊆ closedBall a delta := by
  apply closure_minimal _ isClosed_closedBall
  intro w hw
  have H := pole_tsupport_subset delta hdelta m j
    (subset_closure (show w - a ∈ Function.support (pole delta hdelta m j) from hw))
  simpa only [mem_closedBall, dist_zero_right, dist_eq_norm, sub_zero] using H

theorem translatedPole_hasCompactSupport (delta : ℝ) (hdelta : 0 < delta) (m j : ℕ)
    (a : ComplexVector n) : HasCompactSupport (translatedPole delta hdelta m j a) :=
  (isCompact_closedBall a delta).of_isClosed_subset
    (isClosed_tsupport _) (translatedPole_tsupport_subset delta hdelta m j a)

theorem translatedPole_nonpos (delta : ℝ) (hdelta : 0 < delta) (m j : ℕ)
    (a w : ComplexVector n) : translatedPole delta hdelta m j a w ≤ 0 :=
  pole_nonpos delta hdelta m j (w - a)

theorem translatedPole_antitone (delta : ℝ) (hdelta : 0 < delta) (m : ℕ)
    (a w : ComplexVector n) : Antitone (fun j => translatedPole delta hdelta m j a w) :=
  pole_antitone delta hdelta m (w - a)

theorem translatedPole_eq_on_inner (delta : ℝ) (hdelta : 0 < delta) (m j : ℕ)
    (a : ComplexVector n) {w : ComplexVector n} (hw : w ∈ closedBall a (delta / 2)) :
    translatedPole delta hdelta m j a w =
      (m : ℝ) * (Real.log (‖w - a‖ ^ 2 + poleEpsilon j) - Real.log (1 + delta ^ 2)) :=
  pole_eq_on_inner delta hdelta m j
    (by simpa only [mem_closedBall, dist_zero_right, dist_eq_norm, sub_zero] using hw)

theorem translatedPole_germ_at_center (delta : ℝ) (hdelta : 0 < delta) (m j : ℕ)
    (a : ComplexVector n) :
    translatedPole delta hdelta m j a =ᶠ[𝓝 a]
      (fun w => (m : ℝ) * (Real.log (‖w - a‖ ^ 2 + poleEpsilon j) -
        Real.log (1 + delta ^ 2))) := by
  have hshift : Tendsto (fun w : ComplexVector n => w - a) (𝓝 a) (𝓝 0) := by
    have hc : Continuous (fun w : ComplexVector n => w - a) :=
      continuous_id.sub continuous_const
    have H : Tendsto (fun w : ComplexVector n => w - a) (𝓝 a) (𝓝 (a - a)) := hc.continuousAt
    simpa only [sub_self] using H
  exact hshift.eventually (pole_germ_at_zero delta hdelta m j)

theorem translatedPole_zero_germ_outside (delta : ℝ) (hdelta : 0 < delta) (m j : ℕ)
    (a : ComplexVector n) {w : ComplexVector n} (hw : w ∉ closedBall a delta) :
    translatedPole delta hdelta m j a =ᶠ[𝓝 w] (fun _ => 0) :=
  notMem_tsupport_iff_eventuallyEq.mp
    (fun H => hw (translatedPole_tsupport_subset delta hdelta m j a H))

theorem translatedPole_complexLevi (delta : ℝ) (hdelta : 0 < delta) (m j : ℕ)
    (a w v : ComplexVector n) :
    complexLeviQuadratic (translatedPole delta hdelta m j a) w v =
      complexLeviQuadratic (pole delta hdelta m j) (w - a) v := by
  have hT : ContDiffAt ℂ 2 (fun z : ComplexVector n => z - a) w :=
    (contDiff_id.sub contDiff_const).contDiffAt
  have hf : ContDiffAt ℝ 2 (pole delta hdelta m j) (w - a) :=
    (pole_contDiff delta hdelta m j).contDiffAt.of_le (by simp)
  have H := complexLeviQuadratic_comp hT hf v
  change complexLeviQuadratic (translatedPole delta hdelta m j a) w v = _ at H
  have hD : fderiv ℂ (fun z : ComplexVector n => z - a) w =
      ContinuousLinearMap.id ℂ (ComplexVector n) :=
    ((hasFDerivAt_id w).sub_const a).fderiv
  simpa only [hD, ContinuousLinearMap.id_apply] using H

theorem exists_translatedPole_uniform_levi_lower (delta : ℝ) (hdelta : 0 < delta)
    (m : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : ComplexVector n) (j : ℕ) (w v : ComplexVector n),
      -C * ‖v‖ ^ 2 ≤ complexLeviQuadratic (translatedPole delta hdelta m j a) w v := by
  obtain ⟨C, hC, hbound⟩ := exists_pole_uniform_levi_lower (n := n) delta hdelta m
  refine ⟨C, hC, ?_⟩
  intro a j w v
  rw [translatedPole_complexLevi]
  exact hbound j (w - a) v

end Yau.Proofs.C03Aux.TargetPole
