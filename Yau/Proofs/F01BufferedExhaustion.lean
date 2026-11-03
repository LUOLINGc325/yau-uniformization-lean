import Yau.Proofs.F01OrdinaryMetricData
import Yau.Proofs.F01FiniteCompactJets

/-! Actual finite ordinary-chart buffers and one coordinate-gradient bound
on a compact sublevel, chosen before selecting a chart for a point. -/
open Set Metric
open scoped Manifold ContDiff
noncomputable section
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ} (M : ComplexManifold n)

theorem finite_buffered_exhaustion_data {K : Set M.Carrier}
    (hK : IsCompact K) (hne : K.Nonempty) {u : M.Carrier → ℝ} (hu : SmoothFn u) :
    ∃ (r : M.Carrier → ℝ) (s : Finset M.Carrier) (A : ℝ),
      (∀ p, 0 < r p ∧ closedBall (chartPt p p) (4 * r p) ⊆ chartTarget p) ∧
      s.Nonempty ∧ 0 < A ∧
      (K ⊆ ⋃ p ∈ s, ordinaryChart p '' ball (chartPt p p) (r p)) ∧
      ∀ p ∈ s, ∀ z ∈ ball (chartPt p p) (4 * r p),
        ‖fderiv ℝ (fun w => u (ordinaryChart p w)) z‖ ≤ A := by
  classical
  obtain ⟨r, s, hr, hcover⟩ := finite_buffered_chart_cover M hK
  have hs : s.Nonempty := by
    by_contra hnot
    have hs0 : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnot
    obtain ⟨x, hx⟩ := hne
    have h := hcover hx
    simpa [hs0] using h
  let U : M.Carrier → Set (ComplexVector n) := fun p => chartTarget p
  let B : M.Carrier → Set (ComplexVector n) := fun p => closedBall (chartPt p p) (4 * r p)
  have hU : ∀ p, IsOpen (U p) := fun p => isOpen_extChartAt_target (I := ComplexModel n) p
  have hB : ∀ p, IsCompact (B p) := fun p => isCompact_closedBall _ _
  have hBU : ∀ p, B p ⊆ U p := fun p => (hr p).2
  have hfu : ∀ p, ContDiffOn ℝ ∞ (fun w => u (ordinaryChart p w)) (U p) :=
    fun p => ordinary_coordinate_contDiffOn hu p
  obtain ⟨A, hA, hgrad⟩ := finite_compact_fderiv_budget s U B hU hB hBU
    (fun p w => u (ordinaryChart p w)) hfu
  refine ⟨r, s, A, hr, hs, hA, ?_, ?_⟩
  · simpa only [ordinaryChart] using hcover
  · intro p hp z hz
    exact hgrad p hp z (ball_subset_closedBall hz)

end Yau.NodeProofs.F01Aux
