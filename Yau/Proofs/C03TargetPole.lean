import Yau.Proofs.C03TargetPoleTranslation
import Yau.Proofs.C03TargetPoleLimits

/-! Uniform actual normalized logarithmic poles, before the index and the translation center. -/
noncomputable section
open scoped Topology ContDiff
open Set Filter Metric
namespace Yau.Proofs.C03Aux.TargetPole
open Yau Yau.NodeProofs.P03Aux Yau.LeafProofs.L22Aux
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

theorem translatedPole_ratio (delta : ℝ) (hdelta : 0 < delta) (m j : ℕ)
    (a w : ComplexVector n) : translatedPole delta hdelta m j a w =
      (m : ℝ) * cutoff delta hdelta (w - a) *
        Real.log ((‖w - a‖ ^ 2 + poleEpsilon j) / (1 + delta ^ 2)) :=
  regularizedPole_ratio delta hdelta m (poleEpsilon_pos j) (w - a)

theorem translatedPole_center_tendsto_atBot (delta : ℝ) (hdelta : 0 < delta)
    {m : ℕ} (hm : 0 < m) (a : ComplexVector n) :
    Tendsto (fun j => translatedPole delta hdelta m j a a) atTop atBot := by
  simpa only [translatedPole, sub_self] using pole_zero_tendsto_atBot (n := n) delta hdelta hm

theorem translatedPole_tendsto_away (delta : ℝ) (hdelta : 0 < delta) (m : ℕ)
    (a : ComplexVector n) {w : ComplexVector n} (hw : w ≠ a) :
    Tendsto (fun j => translatedPole delta hdelta m j a w) atTop
      (𝓝 ((m : ℝ) * cutoff delta hdelta (w - a) *
        (Real.log (‖w - a‖ ^ 2) - Real.log (1 + delta ^ 2)))) :=
  pole_tendsto_away delta hdelta m (sub_ne_zero.mpr hw)

theorem uniform_target_poles (delta : ℝ) (hdelta : 0 < delta) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ComplexVector n,
      (∀ w, Antitone (fun j => translatedPole delta hdelta m j a w)) ∧
      ∀ j : ℕ,
        ContDiff ℝ ∞ (translatedPole delta hdelta m j a) ∧
        HasCompactSupport (translatedPole delta hdelta m j a) ∧
        tsupport (translatedPole delta hdelta m j a) ⊆ closedBall a delta ∧
        (∀ w, translatedPole delta hdelta m j a w ≤ 0) ∧
        (∀ w ∈ closedBall a (delta / 2),
          translatedPole delta hdelta m j a w =
            (m : ℝ) * (Real.log (‖w - a‖ ^ 2 + poleEpsilon j) -
              Real.log (1 + delta ^ 2))) ∧
        translatedPole delta hdelta m j a =ᶠ[𝓝 a]
          (fun w => (m : ℝ) * (Real.log (‖w - a‖ ^ 2 + poleEpsilon j) -
            Real.log (1 + delta ^ 2))) ∧
        (∀ w ∉ closedBall a delta,
          translatedPole delta hdelta m j a =ᶠ[𝓝 w] (fun _ => 0)) ∧
        ∀ w v, -C * ‖v‖ ^ 2 ≤
          complexLeviQuadratic (translatedPole delta hdelta m j a) w v := by
  obtain ⟨C, hC, hbound⟩ := exists_translatedPole_uniform_levi_lower (n := n) delta hdelta m
  refine ⟨C, hC, ?_⟩
  intro a
  refine ⟨translatedPole_antitone delta hdelta m a, ?_⟩
  intro j
  exact ⟨translatedPole_contDiff delta hdelta m j a,
    translatedPole_hasCompactSupport delta hdelta m j a,
    translatedPole_tsupport_subset delta hdelta m j a,
    translatedPole_nonpos delta hdelta m j a,
    (fun _ hw => translatedPole_eq_on_inner delta hdelta m j a hw),
    translatedPole_germ_at_center delta hdelta m j a,
    (fun _ hw => translatedPole_zero_germ_outside delta hdelta m j a hw),
    hbound a j⟩

end Yau.Proofs.C03Aux.TargetPole
