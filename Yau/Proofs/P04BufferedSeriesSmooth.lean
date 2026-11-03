import Yau.Proofs.P04BufferedModels
import Yau.Proofs.P04LeviCharts

noncomputable section
open Set Filter
open scoped Topology Manifold ContDiff BigOperators

namespace Yau.Proofs.P04Aux
open Yau Yau.LeafProofs
variable {n : ℕ} {M : ComplexManifold n}

/-- Smoothness of the same global series in EVERY original chart follows
from its actual smooth buffered models and the genuine chart transitions. -/
theorem smoothFn_tsum_of_buffered_charts (a : ℕ → M.Carrier) (ρ : ℕ → ℝ)
    (β : ℕ → ComplexVector n → ℝ)
    (hone : ∀ j z, z ∈ Metric.closedBall (chartPt (a j) (a j)) (ρ j) → β j z=1)
    (hcover : ∀ x : M.Carrier, ∃ j, x ∈ (extChartAt (ComplexModel n) (a j)).source ∧
      chartPt (a j) x ∈ Metric.ball (chartPt (a j) (a j)) (ρ j/2))
    (hρ : ∀ j, 0 < ρ j) (f : ℕ → M.Carrier → ℝ) (c : ℕ → ℝ)
    (hmodels : ∀ j, ContDiff ℝ ∞
      (fun z => ∑' i, c i*(β j z*inChart (a j) (f i) z))) :
    SmoothFn (fun x => ∑' i, c i*f i x) := by
  intro p z hz
  obtain ⟨j,hy,hinner⟩ := hcover (chartInv p z)
  let T : ComplexVector n → ComplexVector n := fun w => chartPt (a j) (chartInv p w)
  have hT : ContDiffAt ℂ ∞ T z := L18Aux.chartTransition_contDiffAt p (a j) hz hy
  have hinner' : T z ∈ Metric.ball (chartPt (a j) (a j)) (ρ j) :=
    Metric.ball_subset_ball (by linarith [hρ j] : ρ j/2 ≤ ρ j) hinner
  have heq : inChart p (fun x => ∑' i, c i*f i x) =ᶠ[𝓝 z]
      ((fun w => ∑' i, c i*(β j w*inChart (a j) (f i) w)) ∘ T) := by
    filter_upwards [(canonicalOverlap_isOpen (a j) p).mem_nhds ⟨hz,hy⟩,
      hT.continuousAt.eventually (Metric.isOpen_ball.mem_nhds hinner')] with w hw hTw
    change (∑' i, c i*f i (chartInv p w))=
      ∑' i, c i*(β j (T w)*f i (chartInv (a j) (T w)))
    apply tsum_congr
    intro i
    rw [hone j (T w) (Metric.ball_subset_closedBall hTw),one_mul,
      show chartInv (a j) (T w)=chartInv p w from
        (extChartAt (ComplexModel n) (a j)).left_inv hw.2]
  exact (((hmodels j).contDiffAt.comp z (hT.restrict_scalars ℝ)).congr_of_eventuallyEq heq).contDiffWithinAt

end Yau.Proofs.P04Aux
