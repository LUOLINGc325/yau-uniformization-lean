import Yau.Proofs.C03ShortLift
import Yau.Proofs.C03ChernGaugeJacobian

/-! The actual target coordinate map on the same inverse sheet is
holomorphic, and its centered coordinate vanishes only at the origin. -/

noncomputable section
open Set Metric
open scoped Topology ContDiff Manifold

namespace Yau.Proofs.C03Aux
open Yau Yau.Blueprint Yau.LeafProofs.L12Aux
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {M : ComplexManifold n}

theorem sheet_image_subset_ball (σ : ComplexVector n → ComplexVector n)
    (W : Set (ComplexVector n)) (r : ℝ) (hmem : MapsTo σ W (ball 0 r)) :
    σ '' W ⊆ ball 0 r := by
  rintro z ⟨w, hw, rfl⟩
  exact hmem hw

theorem sheet_image_target_source (Φ : ComplexVector n → M.Carrier)
    (c : M.Carrier) (W : Set (ComplexVector n)) (hW : W ⊆ chartTarget c)
    (σ : ComplexVector n → ComplexVector n)
    (hright : ∀ w ∈ W, Φ (σ w) = chartInv c w) :
    ∀ z ∈ σ '' W, Φ z ∈ (extChartAt (ComplexModel n) c).source := by
  rintro z ⟨w, hw, rfl⟩
  rw [hright w hw]
  exact (extChartAt (ComplexModel n) c).map_target (hW hw)

theorem sheet_coordinates_holomorphic (Φ : ComplexVector n → M.Carrier)
    (r : ℝ) (hΦ : IsLocalBiholomorphism Φ r)
    (c : M.Carrier) (W : Set (ComplexVector n)) (hW : W ⊆ chartTarget c)
    (σ : ComplexVector n → ComplexVector n) (hmem : MapsTo σ W (ball 0 r))
    (hright : ∀ w ∈ W, Φ (σ w) = chartInv c w) :
    ContDiffOn ℂ ∞ (ShortLift.sheetCoordinates Φ c) (σ '' W) := by
  apply (ChernGauge.coordinate_holomorphic hΦ.1 c).mono
  intro z hz
  exact ⟨sheet_image_subset_ball σ W r hmem hz,
    sheet_image_target_source Φ c W hW σ hright z hz⟩

theorem sheet_coordinates_injective (Φ : ComplexVector n → M.Carrier)
    (c : M.Carrier) (O : Set (ComplexVector n))
    (σ : ComplexVector n → ComplexVector n)
    (hleft : ∀ z ∈ O, σ (ShortLift.sheetCoordinates Φ c z) = z) :
    InjOn (ShortLift.sheetCoordinates Φ c) O := by
  intro z hz y hy heq
  rw [← hleft z hz, ← hleft y hy, heq]

theorem sheet_centered_coordinate_zero_iff (Φ : ComplexVector n → M.Carrier)
    (c : M.Carrier) (W : Set (ComplexVector n)) (w0 : ComplexVector n) (hw0 : w0 ∈ W)
    (σ : ComplexVector n → ComplexVector n) (hσ0 : σ w0 = 0)
    (hθσ : ∀ w ∈ W, ShortLift.sheetCoordinates Φ c (σ w) = w)
    (hσθ : ∀ z ∈ σ '' W, σ (ShortLift.sheetCoordinates Φ c z) = z)
    (z : ComplexVector n) (hz : z ∈ σ '' W) :
    ShortLift.sheetCoordinates Φ c z - w0 = 0 ↔ z = 0 := by
  have hθ0 : ShortLift.sheetCoordinates Φ c 0 = w0 := by
    simpa only [hσ0] using hθσ w0 hw0
  constructor
  · intro heq
    have hcoord : ShortLift.sheetCoordinates Φ c z = w0 := sub_eq_zero.mp heq
    rw [← hσθ z hz, hcoord, hσ0]
  · rintro rfl
    exact sub_eq_zero.mpr hθ0

theorem sheet_compact_inner_image (σ : ComplexVector n → ComplexVector n)
    (w0 : ComplexVector n) (R δ : ℝ) (hRδ : R < δ)
    (hσ : ContinuousOn σ (ball w0 δ)) :
    IsCompact (σ '' closedBall w0 R) ∧ σ '' closedBall w0 R ⊆ σ '' ball w0 δ := by
  have hsub : closedBall w0 R ⊆ ball w0 δ := closedBall_subset_ball hRδ
  exact ⟨(isCompact_closedBall w0 R).image_of_continuousOn (hσ.mono hsub),
    image_mono hsub⟩

end Yau.Proofs.C03Aux
