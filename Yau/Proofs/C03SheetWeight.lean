import Yau.Proofs.C03SheetCoordinates
import Yau.Proofs.C03ChartDistance
import Yau.Proofs.C03ActualEnvelope
import Yau.Proofs.C03GlobalWeight

/-! The same short inverse sheet lies in the uniformly strict part of
one fixed global smooth weight. All radius constants precede the chart. -/

noncomputable section
open Set Filter Metric
open scoped Topology ContDiff Manifold Matrix ComplexOrder

namespace Yau.Proofs.C03Aux
open Yau Yau.Blueprint Yau.LeafProofs L12Aux L23Aux L22Aux
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

theorem exists_sheet_global_weight (hn : 1 ≤ n) (X : KahlerManifold n)
    (Φ : ComplexVector n → Pt X) (r c ρ ε : ℝ) (hr : 0 < r) (hc : 0 < c)
    (hρ : 0 < ρ) (hΦ : IsLocalBiholomorphism Φ r)
    (hlo : ∀ z ∈ ball (0 : ComplexVector n) r,
      HermLE ((c : ℂ) • (1 : Herm n)) (pullbackMat X.metric.form Φ z))
    (hsmall : Real.sqrt ((min c 1)⁻¹) * (2 * ρ) < r / 4) (hρε : 2 * ρ ≤ ε)
    (K K' : Set X.manifold.Carrier) (h0 : Φ 0 ∈ K)
    (hK' : ∀ o ∈ K, ∀ y : X.manifold.Carrier,
      inducedDistance X.metric.form o y ≤ ε → y ∈ K')
    (κ : ℝ) (hκ : 0 < κ)
    (htarget : ∀ y ∈ K', ∀ u v : TangentVector X.manifold y,
      κ * hermitianNormSq (X.metric.form y) u * hermitianNormSq (X.metric.form y) v ≤
        bisectionalForm X.metric.form y (tangentCoords y y u) (tangentCoords y y v))
    (σ : ComplexVector n → ComplexVector n) (w0 : ComplexVector n) (δ δsheet L : ℝ)
    (hδsheet : δ < δsheet) (hL : 0 ≤ L) (hLδ : L * δ < ρ)
    (hσ : ContinuousOn σ (ball w0 δsheet))
    (hσdist : ∀ w ∈ ball w0 δsheet,
      inducedDistance (chartExtendedField hn X Φ r hr hΦ) (0 : ComplexVector n) (σ w) ≤
        L * ‖w - w0‖)
    (ξ : ComplexVector n) (hξ : ξ ≠ 0)
    (hunit : dualNormMat (pullbackMat X.metric.form Φ 0) ξ = 1) :
    ∃ F : ComplexVector n → ℝ, ContDiff ℝ ∞ F ∧
      (∀ z, (leviC F z).PosSemidef) ∧
      (∀ z ∈ ball (0 : ComplexVector n) (r / 4), F z ≤ chartLogBound c ξ + 3) ∧
      ∀ z ∈ σ '' closedBall w0 δ,
        0 ≤ F z ∧ HermLE (((κ / 2 : ℝ) : ℂ) •
          gMat (chartExtendedField hn X Φ r hr hΦ) z) (leviC F z) := by
  let k := chartExtendedField hn X Φ r hr hΦ
  have ks : MetricSmooth k := chartExtendedField_metricSmooth hn X Φ r hr hΦ
  let S : Set (ComplexVector n) := {z | inducedDistance k (0 : ComplexVector n) z < ρ}
  let T := σ '' closedBall w0 δ
  have hS : IsOpen S := isOpen_lt (continuous_distFrom k ks (0 : ComplexVector n)) continuous_const
  have hnorm (z : ComplexVector n) (hz : z ∈ S) : ‖z‖ < r / 8 := by
    have H := euclidean_dist_le_field_distance hn k ks (min c 1) (lt_min hc zero_lt_one)
      (chartExtendedField_lower hn X Φ r c hr hΦ hlo) (0 : ComplexVector n) z
    rw [dist_zero_left] at H
    have H' := mul_le_mul_of_nonneg_left (le_of_lt hz) (Real.sqrt_nonneg ((min c 1)⁻¹))
    nlinarith
  have hSO : S ⊆ ball (0 : ComplexVector n) (r / 2) := by
    intro z hz
    rw [mem_ball, dist_zero_right]
    exact (hnorm z hz).trans (by linarith)
  have hsub : closedBall w0 δ ⊆ ball w0 δsheet := closedBall_subset_ball hδsheet
  have hT : IsCompact T := (isCompact_closedBall w0 δ).image_of_continuousOn (hσ.mono hsub)
  have hTS : T ⊆ S := by
    rintro z ⟨w, hw, rfl⟩
    have H := hσdist w (hsub hw)
    have hw' : ‖w - w0‖ ≤ δ := by simpa only [mem_closedBall, dist_eq_norm] using hw
    exact (H.trans (mul_le_mul_of_nonneg_left hw' hL)).trans_lt hLδ
  have hTD : T ⊆ ball (0 : ComplexVector n) (r / 4) := by
    intro z hz
    rw [mem_ball, dist_zero_right]
    exact (hnorm z (hTS hz)).trans (by linarith)
  obtain ⟨_, g, hg, hgD, hgT⟩ := exists_actual_envelope_smoothing hn X Φ r c ρ (r / 4)
    hr hc hρ (by positivity) (by linarith) hΦ hlo (by nlinarith)
    ξ hξ hunit K' κ hκ htarget S T hS hSO hT hTS hTD
    (fun z hz => by
      rw [inducedDistance_symm k ks z (0 : ComplexVector n)]
      exact le_of_lt hz)
    (fun z hz y _ hzy => chart_moving_ball_target_fence hn X Φ r c ρ ε hr hc hΦ hlo
      hsmall hρε K K' h0 hK' z y (le_of_lt hz) hzy)
  have hTclosed : T ⊆ closedBall (0 : ComplexVector n) (r / 8) := by
    intro z hz
    rw [mem_closedBall, dist_zero_right]
    exact (hnorm z (hTS hz)).le
  obtain ⟨F, hF, hFp, hFu, hFgerm⟩ := exists_global_psh_weight (r / 4) (r / 8)
    (chartLogBound c ξ) (by positivity) (by positivity) (by linarith)
    (chartLogBound_nonneg c ξ) g hg (fun z hz => (hgD z hz).1)
    (fun z hz => (hgD z hz).2) T hTclosed (fun z hz => (hgT z hz).1)
  refine ⟨F, hF, hFp, hFu, ?_⟩
  intro z hz
  have heq := hFgerm z hz
  exact ⟨by rw [heq.eq_of_nhds]; exact (hgT z hz).1,
    by rw [leviC_congr_germ heq]; exact (hgT z hz).2⟩

end Yau.Proofs.C03Aux
