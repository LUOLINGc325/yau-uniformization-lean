import Yau.Proofs.C03SheetCoordinates
import Yau.Proofs.C03SeedInverseBound
import Yau.Proofs.C03ChartNaturality

/-! The same sheet has the actual Jacobian congruence and the exact
source differential lower bound required for the seed and pole estimates. -/

noncomputable section
open Set Metric
open scoped Topology ContDiff Manifold Matrix ComplexOrder
namespace Yau.Proofs.C03Aux
open Yau Yau.Blueprint Yau.LeafProofs L12Aux L17Aux
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

theorem chart_sheet_point_metric (hn : 1 ≤ n) (X : KahlerManifold n)
    (Φ : ComplexVector n → Pt X) (r : ℝ) (hr : 0 < r)
    (hΦ : IsLocalBiholomorphism Φ r) (a : X.manifold.Carrier)
    (W : Set (ComplexVector n)) (hW : W ⊆ chartTarget a)
    (σ : ComplexVector n → ComplexVector n) (hmem : MapsTo σ W (ball 0 (r / 2)))
    (hright : ∀ w ∈ W, Φ (σ w) = chartInv a w)
    (z : ComplexVector n) (hz : z ∈ σ '' W) :
    let θ := ShortLift.sheetCoordinates Φ a
    let J := linearMatrix (fderiv ℂ θ z)
    IsUnit J.det ∧ (hMat X.metric.form a (θ z)).PosDef ∧
      gMat (chartExtendedField hn X Φ r hr hΦ) z = Jᴴ * hMat X.metric.form a (θ z) * J := by
  have hzr : z ∈ ball (0 : ComplexVector n) r :=
    (ball_subset_ball (by linarith)) (sheet_image_subset_ball σ W (r / 2) hmem hz)
  have hzi : z ∈ ball (0 : ComplexVector n) (3 * r / 4) :=
    (ball_subset_ball (by linarith)) (sheet_image_subset_ball σ W (r / 2) hmem hz)
  have hsrc := sheet_image_target_source Φ a W hW σ hright z hz
  have hΦd := (hΦ.1.contMDiffAt (isOpen_ball.mem_nhds hzr)).mdifferentiableAt (by simp)
  have hJi := ChernGauge.jacobian_injective Φ a z hΦd hsrc (hΦ.2 z hzr)
  exact ⟨isUnit_iff_ne_zero.mpr (linearMatrix_det_ne_zero _ hJi),
    Yau.LeafProofs.L12Aux.hMat_posDef X.metric.form a _
      ((extChartAt (ComplexModel n) a).map_source hsrc),
    ChernGauge.source_gMat_congruence hn (chartExtendedField hn X Φ r hr hΦ)
      X.metric.form Φ z a hΦd hsrc
      (chartExtendedField_pullback hn X Φ r hr hΦ z hzi)⟩

theorem chart_sheet_differential_lower (hn : 1 ≤ n) (X : KahlerManifold n)
    (Φ : ComplexVector n → Pt X) (r : ℝ) (hr : 0 < r)
    (hΦ : IsLocalBiholomorphism Φ r) (a : X.manifold.Carrier)
    (W : Set (ComplexVector n)) (hW : W ⊆ chartTarget a)
    (σ : ComplexVector n → ComplexVector n) (hmem : MapsTo σ W (ball 0 (r / 2)))
    (hright : ∀ w ∈ W, Φ (σ w) = chartInv a w)
    (d : ℝ) (hlo : ∀ z ∈ σ '' W,
      HermLE ((d : ℂ) • (1 : Herm n)) (hMat X.metric.form a (ShortLift.sheetCoordinates Φ a z)))
    (z : ComplexVector n) (hz : z ∈ σ '' W) (v : ComplexVector n) :
    d * ‖fderiv ℂ (ShortLift.sheetCoordinates Φ a) z v‖ ^ 2 ≤
      Yau.NodeProofs.E01Aux.ellipsoidQuadratic (gMat (chartExtendedField hn X Φ r hr hΦ) z) v :=
  differential_quadratic_lower _ _ _ d
    (chart_sheet_point_metric hn X Φ r hr hΦ a W hW σ hmem hright z hz).2.2
    (hlo z hz) v

end Yau.Proofs.C03Aux
