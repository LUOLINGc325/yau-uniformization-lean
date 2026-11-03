import Yau.Proofs.F05CrossCutoffs
import Yau.Proofs.F05BufferedComposition

/-! Each actual supported manifold patch has a uniform Schauder budget in
every other flattened chart, preserving its separate small lower budget. -/

open Set Filter
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types true
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

def F05CrossChartPatch (A : AtlasData M) (i j : Fin A.count)
    (β : M.Carrier → ℝ) (v : Point n → ℝ) (p : Point n) : ℝ :=
  F05CrossCutoff A i β p.1 * v (F05Transition A i j p.1,p.2)

theorem F05_cross_chart_patch_budget {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (i j : Fin A.count) {β : M.Carrier → ℝ}
    (hβ : SmoothFn β) (hSupport : tsupport β ⊆ lift A j '' Metric.closedBall 0 (3/4))
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T K0 L0 : ℝ) (v : Point n → ℝ), T ≤ 1 →
      SchauderBound α (cylinder univ 0 T) v K0 →
      HolderBound α (cylinder univ 0 T) (fun p => (v p,spatialD v p)) L0 →
      SchauderBound α (cylinder univ 0 T) (F05CrossChartPatch A i j β v) (C*(K0+L0)) ∧
        HolderBound α (cylinder univ 0 T)
          (fun p => (F05CrossChartPatch A i j β v p,spatialD (F05CrossChartPatch A i j β v) p)) (C*L0) := by
  exact F05_buffered_composition_budget hα hα1 (F05TransitionDomain_isOpen hA i j)
    ((F05Transition_contDiffOn hA i j).of_le (by simp))
    (F05CrossCutoff_contDiff hA i hβ) (F05CrossCutoff_compactSupport A i β)
    (F05CrossCutoff_tsupport_transition hA i j hSupport)

theorem F05CrossChartPatch_eq_near (A : AtlasData M) (i j : Fin A.count)
    (β : M.Carrier → ℝ) (v : Point n → ℝ) {z : Space n} (hz : z ∈ F05D A i) :
    ∀ᶠ w in 𝓝 z, ∀ t : ℝ, F05CrossChartPatch A i j β v (w,t) =
      β (lift A i w)*v (F05Coord A j (lift A i w),t) := by
  have hzBall : z ∈ Metric.ball (0 : Space n) (21/10) := by
    rw [Metric.mem_ball,dist_zero_right]
    linarith [hz.1]
  filter_upwards [Metric.isOpen_ball.mem_nhds hzBall] with w hw t
  unfold F05CrossChartPatch
  have hn : ‖w‖ < 21/10 := by simpa only [Metric.mem_ball,dist_zero_right] using hw
  rw [F05CrossCutoff_eq i β hn.le]
  rfl

end Yau.Proofs.F05Aux
