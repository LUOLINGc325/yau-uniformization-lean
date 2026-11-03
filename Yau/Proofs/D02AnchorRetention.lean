import Yau.Proofs.D02ConcentrationDomain
import Yau.Proofs.D02MovingAnchors

/-! A single compact subset of the regular domain meets every actual
moving positive-area anchor. Countable atoms have zero planar area. -/

open scoped Topology ENNReal
open MeasureTheory Filter Set Metric

noncomputable section
namespace Yau.NodeProofs.D02Aux
open Yau Yau.Blueprint

theorem exists_compact_regular_anchor_set (μ : Measure ℂ)
    (hμ : ∀ K : Set ℂ, IsCompact K → K ⊆ ball (0 : ℂ) 1 → μ K < ⊤)
    (S : ℕ → Set ℂ)
    (hS : ∀ j, ENNReal.ofReal (5 * Real.pi / 32) ≤ volume (S j) ∧
      S j ⊆ {z : ℂ | (1 / 2 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 3 / 4}) :
    ∃ H : Set ℂ, IsCompact H ∧ H ⊆ regularPotentialDomain (ball (0 : ℂ) 1) μ ∧
      ∀ j, (S j ∩ H).Nonempty := by
  let Z := concentrationAtoms (ball (0 : ℂ) 1) μ
  have hZ : Z.Countable := concentrationAtoms_countable isOpen_ball μ hμ
  obtain ⟨O, hZO, hO, hsmall⟩ := Z.exists_isOpen_lt_of_lt
    (ENNReal.ofReal (5 * Real.pi / 32)) (by rw [hZ.measure_zero volume]; positivity)
  let H : Set ℂ := {z : ℂ | (1 / 2 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 3 / 4} \ O
  have hH : IsCompact H := anchorCompactAnnulus_isCompact.diff hO
  have hHD : H ⊆ regularPotentialDomain (ball (0 : ℂ) 1) μ := by
    intro z hz
    have hzD : z ∈ ball (0 : ℂ) 1 := by
      rw [mem_ball, dist_zero_right]
      exact hz.1.2.trans_lt (by norm_num)
    refine ⟨hzD, lt_of_not_ge ?_⟩
    intro hatom
    exact hz.2 (hZO ⟨hzD, hatom⟩)
  refine ⟨H, hH, hHD, fun j => ?_⟩
  have hnsub : ¬S j ⊆ O := fun h => (not_le_of_gt hsmall) ((hS j).1.trans (measure_mono h))
  obtain ⟨z, hzS, hzO⟩ := not_subset.mp hnsub
  exact ⟨z, hzS, (hS j).2 hzS, hzO⟩

end Yau.NodeProofs.D02Aux
