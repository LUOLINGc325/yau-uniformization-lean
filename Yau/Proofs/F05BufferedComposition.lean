import Yau.Proofs.F05CompactSmoothExtension
import Yau.Proofs.F05SpatialCutoffHolder
import Yau.LeafProofs.L16ChartCutoffSchauder

/-! A compactly supported physical chart composition has genuine full and
lower Holder budgets, uniform before time and the function being composed. -/

open Set
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types true
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux

theorem F05_buffered_composition_budget {n : ℕ} {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) {V : Set (Space n)} (hV : IsOpen V)
    {ψ : Space n → Space n} (hψ : ContDiffOn ℝ 3 ψ V)
    {φ : Space n → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hSupport : tsupport φ ⊆ V) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T K0 L0 : ℝ) (u : Point n → ℝ), T ≤ 1 →
      SchauderBound α (cylinder univ 0 T) u K0 →
      HolderBound α (cylinder univ 0 T) (fun p => (u p,spatialD u p)) L0 →
      let w := fun p : Point n => φ p.1*u (ψ p.1,p.2)
      SchauderBound α (cylinder univ 0 T) w (C*(K0+L0)) ∧
        HolderBound α (cylinder univ 0 T) (fun p => (w p,spatialD w p)) (C*L0) := by
  obtain ⟨G,hG,hEqG⟩ := F05_compact_smooth_extension hV hc hSupport hψ
  obtain ⟨R,hR⟩ := Metric.isBounded_iff_subset_closedBall (0 : Space n) |>.mp hc.isBounded
  let r : ℝ := 1+|R|
  have hSupportBall : tsupport φ ⊆ Metric.ball 0 r := by
    intro x hx
    exact Metric.closedBall_subset_ball (by dsimp only [r]; linarith [le_abs_self R]) (hR hx)
  obtain ⟨P,hP,hCutoff⟩ := F05_smooth_cutoff_three_holder hφ hc
  have hCut := hCutoff α hα hα1
  obtain ⟨C,hC,hBudget⟩ := compact_chart_cutoff_full_schauder hα hα1 isOpen_univ
    (isCompact_closedBall (0 : Space n) r) (convex_closedBall (0 : Space n) r)
    (subset_univ _) Metric.isOpen_ball Metric.ball_subset_closedBall hG.contDiffOn
    (hφ.of_le (by simp)) hSupportBall
    (holderBound_mono hCut.1 (subset_univ _))
    (holderBound_mono hCut.2.1 (subset_univ _))
    (holderBound_mono hCut.2.2 (subset_univ _))
  refine ⟨C,hC,?_⟩
  intro T K0 L0 u hT hu hLow
  have hFunctions : (fun p : Point n => φ p.1*u (G p.1,p.2)) =
      (fun p : Point n => φ p.1*u (ψ p.1,p.2)) := by
    funext p
    by_cases hp : φ p.1 = 0
    · simp only [hp,zero_mul]
    · rw [hEqG (subset_tsupport φ hp)]
  have h := hBudget T K0 L0 u hT hu hLow
  dsimp only at h ⊢
  have hPoint (p : Point n) := congrFun hFunctions p
  simpa only [hFunctions,hPoint] using h

end Yau.Proofs.F05Aux
