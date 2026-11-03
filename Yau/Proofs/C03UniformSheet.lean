import Yau.Proofs.C03SheetCoordinates
import Yau.Proofs.C03SheetWeight
import Yau.Proofs.C03TargetChartsRecenter
import Yau.Proofs.C03TargetCurvature

/-! Uniform target and source radii are selected before the original map.
The resulting sheet is the genuine holomorphic inverse with its actual source distance. -/

noncomputable section
open Set Metric
open scoped Topology ContDiff Manifold Matrix ComplexOrder
namespace Yau.Proofs.C03Aux
open Yau Yau.Blueprint Yau.LeafProofs L12Aux L23Aux
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}
local instance (hn : 1 ≤ n) : NormedAddCommGroup (ComplexEuclideanManifold n hn).Carrier :=
  inferInstanceAs (NormedAddCommGroup (ComplexVector n))
local instance (hn : 1 ≤ n) : NormedSpace ℝ (ComplexEuclideanManifold n hn).Carrier :=
  inferInstanceAs (NormedSpace ℝ (ComplexVector n))
local instance (hn : 1 ≤ n) : NormedSpace ℂ (ComplexEuclideanManifold n hn).Carrier :=
  inferInstanceAs (NormedSpace ℂ (ComplexVector n))

theorem exists_uniform_source_sheets (hn : 1 ≤ n) (X : KahlerManifold n)
    (r c : ℝ) (hr : 0 < r) (hc : 0 < c)
    (K : Set X.manifold.Carrier) (hK : IsCompact K) :
    ∃ (K' : Set X.manifold.Carrier) (ε κ d U L ρ δ : ℝ),
      0 < ε ∧ 0 < κ ∧ 0 < d ∧ 0 < U ∧ 0 < L ∧ 0 < ρ ∧ 0 < δ ∧
      2 * ρ ≤ ε ∧ Real.sqrt ((min c 1)⁻¹) * (2 * ρ) < r / 4 ∧ L * δ < ρ ∧
      (∀ o ∈ K, ∀ y : X.manifold.Carrier,
        inducedDistance X.metric.form o y ≤ ε → y ∈ K') ∧
      (∀ y ∈ K', ∀ u v : TangentVector X.manifold y,
        κ * hermitianNormSq (X.metric.form y) u * hermitianNormSq (X.metric.form y) v ≤
          bisectionalForm X.metric.form y (tangentCoords y y u) (tangentCoords y y v)) ∧
      ∀ (Φ : ComplexVector n → Pt X) (hΦ : IsLocalBiholomorphism Φ r),
        Φ 0 ∈ K →
        (∀ z ∈ ball (0 : ComplexVector n) r,
          HermLE ((c : ℂ) • (1 : Herm n)) (pullbackMat X.metric.form Φ z)) →
        ∃ (a : X.manifold.Carrier) (σ : ComplexVector n → ComplexVector n),
          let w0 := chartPt a (Φ 0)
          ball w0 δ ⊆ chartTarget a ∧
          (∀ w ∈ ball w0 δ,
            HermLE ((d : ℂ) • (1 : Herm n)) (hMat X.metric.form a w) ∧
            HermLE (hMat X.metric.form a w) ((U : ℂ) • (1 : Herm n))) ∧
          σ w0 = 0 ∧ ContDiffOn ℂ ∞ σ (ball w0 δ) ∧
          MapsTo σ (ball w0 δ) (ball 0 (r / 2)) ∧
          (∀ w ∈ ball w0 δ, Φ (σ w) = chartInv a w) ∧
          IsOpen (σ '' ball w0 δ) ∧
          (∀ w ∈ ball w0 δ, ShortLift.sheetCoordinates Φ a (σ w) = w) ∧
          (∀ z ∈ σ '' ball w0 δ, σ (ShortLift.sheetCoordinates Φ a z) = z) ∧
          ∀ w ∈ ball w0 δ,
            inducedDistance (chartExtendedField hn X Φ r hr hΦ) (0 : ComplexVector n) (σ w) ≤
              L * ‖w - w0‖ := by
  obtain ⟨K', ε, hK'c, hε, _, hfence⟩ := exists_compact_target_neighborhood X K hK
  obtain ⟨κ, hκ, hcurv⟩ := compact_chern_bisectional_lower_bound X K' hK'c
  obtain ⟨I, rt, d, U, L, δstar, hd, hU, hL, hδstar, hcharts⟩ :=
    TargetCharts.exists_uniform_recentered_charts X.metric K hK
  obtain ⟨ρ, hρ, hρε, hsmall⟩ := exists_chart_transport_radius r ε hr hε (min c 1)
  let δ := min δstar (min (ρ / (4 * L)) (Real.sqrt (2 * c) * r / (4 * L))) / 2
  have hδ : 0 < δ := by
    dsimp only [δ]
    exact div_pos (lt_min hδstar (lt_min (by positivity) (by positivity))) (by norm_num)
  have hδstar' : δ ≤ δstar := by
    have H := min_le_left δstar (min (ρ / (4 * L)) (Real.sqrt (2 * c) * r / (4 * L)))
    dsimp only [δ]
    linarith
  have hδρ : L * δ < ρ := by
    have H := (min_le_right δstar (min (ρ / (4 * L)) (Real.sqrt (2 * c) * r / (4 * L)))).trans
      (min_le_left _ _)
    have H' := (le_div_iff₀ (by positivity : 0 < 4 * L)).mp H
    dsimp only [δ]
    nlinarith
  have hshort : L * δ < Real.sqrt (2 * c) * (r / 2) := by
    have H := (min_le_right δstar (min (ρ / (4 * L)) (Real.sqrt (2 * c) * r / (4 * L)))).trans
      (min_le_right _ _)
    have H' := (le_div_iff₀ (by positivity : 0 < 4 * L)).mp H
    dsimp only [δ]
    nlinarith [Real.sqrt_pos.mpr (by positivity : 0 < 2 * c)]
  refine ⟨K', ε, κ, d, U, L, ρ, δ, hε, hκ, hd, hU, hL, hρ, hδ,
    hρε, hsmall, hδρ, hfence, hcurv, ?_⟩
  intro Φ hΦ h0 hlo
  obtain ⟨a, _, hsrc, _, _, hchart⟩ := hcharts (Φ 0) h0
  obtain ⟨hW, hmetric⟩ := hchart δ hδ hδstar'
  have hsub : ball (0 : ComplexVector n) (r / 2) ⊆ ball 0 r := ball_subset_ball (by linarith)
  have hΦhalf : IsLocalBiholomorphism Φ (r / 2) :=
    ⟨hΦ.1.mono hsub, fun z hz => hΦ.2 z (hsub hz)⟩
  have hp0 : Φ 0 = chartInv a (chartPt a (Φ 0)) :=
    ((extChartAt (ComplexModel n) a).left_inv hsrc).symm
  obtain ⟨σ, hσ0, hσ, hσmem, hright, _, _, hopen, hθσ, hσθ, hdist⟩ :=
    ShortLift.exists_short_holomorphic_inverse_sheet X.metric.form
      (metricSmooth_of_smoothMetric X.metric) Φ (r / 2) c (by positivity) hc hΦhalf
      (fun z hz => hlo z (hsub hz)) a (chartPt a (Φ 0)) δ L hδ hL hW hp0
      (fun w hw => (hmetric w hw).2.2) hshort
  refine ⟨a, σ, hW, fun w hw => ⟨(hmetric w hw).1, (hmetric w hw).2.1⟩,
    hσ0, hσ, hσmem, hright, hopen, hθσ, hσθ, ?_⟩
  apply hdist hn (chartExtendedField hn X Φ r hr hΦ)
    (chartExtendedField_metricSmooth hn X Φ r hr hΦ)
  intro z hz u v
  have hz' : (z : ComplexVector n) ∈ ball (0 : ComplexVector n) (r / 2) := hz
  have hi : (z : ComplexVector n) ∈ ball (0 : ComplexVector n) (3 * r / 4) :=
    ball_subset_ball (by linarith) hz'
  exact chartExtendedField_pullback hn X Φ r hr hΦ z hi u v

end Yau.Proofs.C03Aux
