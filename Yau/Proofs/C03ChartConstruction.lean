import Yau.Proofs.C03UniformSheet
import Yau.Proofs.C03SheetMetric
import Yau.Proofs.C03SheetCovector
import Yau.Proofs.C03SheetWeightedPoles
import Yau.Proofs.C03SheetSourceBound
import Yau.Proofs.C03SheetLocalSeed
import Yau.Proofs.C03ScalarSolution
import Yau.Proofs.C03CorrectionJets

/-! Actual chart geometry, the fixed smooth L14 background, and the same
critical-pole representative produce the scalar estimate data used by C03. -/

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff Manifold Matrix ComplexOrder ENNReal
namespace Yau.Proofs.C03Aux
open Yau Yau.Blueprint Yau.LeafProofs L12Aux L23Aux L17Aux L22Aux L14Aux
open Yau.NodeProofs.E01Aux
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}
local instance (hn : 1 ≤ n) : NormedAddCommGroup (ComplexEuclideanManifold n hn).Carrier :=
  inferInstanceAs (NormedAddCommGroup (ComplexVector n))
local instance (hn : 1 ≤ n) : NormedSpace ℝ (ComplexEuclideanManifold n hn).Carrier :=
  inferInstanceAs (NormedSpace ℝ (ComplexVector n))
local instance (hn : 1 ≤ n) : NormedSpace ℂ (ComplexEuclideanManifold n hn).Carrier :=
  inferInstanceAs (NormedSpace ℂ (ComplexVector n))

theorem chart_scalar_estimate_data (hn : 1 ≤ n) (X : KahlerManifold n)
    (r c ρ ε κ d U L δ δs δp Cp G : ℝ) (hr : 0 < r) (hc : 0 < c)
    (hρ : 0 < ρ) (hκ : 0 < κ) (hd : 0 < d) (hU : 0 < U) (hL : 0 < L)
    (hδ : 0 < δ) (hδs : 0 < δs) (hδp : 0 < δp)
    (hδsδ : δs < δ) (hsep : δp < δs / 2) (hLδs : L * δs < ρ)
    (hCp : 0 ≤ Cp) (hG : 0 ≤ G)
    (hsmall : Real.sqrt ((min c 1)⁻¹) * (2 * ρ) < r / 4) (hρε : 2 * ρ ≤ ε)
    (K K' : Set X.manifold.Carrier)
    (hfence : ∀ o ∈ K, ∀ y : X.manifold.Carrier,
      inducedDistance X.metric.form o y ≤ ε → y ∈ K')
    (hcurv : ∀ y ∈ K', ∀ u v : TangentVector X.manifold y,
      κ * hermitianNormSq (X.metric.form y) u * hermitianNormSq (X.metric.form y) v ≤
        bisectionalForm X.metric.form y (tangentCoords y y u) (tangentCoords y y v))
    (hPole : ∀ (a : ComplexVector n) (j : ℕ) (w v : ComplexVector n),
      -Cp * ‖v‖ ^ 2 ≤ complexLeviQuadratic (TargetPole.translatedPole δp hδp (n + 1) j a) w v)
    (hcut : ∀ w : ComplexVector n, ‖seedCutoffDbar δs hδs w‖ ≤ G)
    (Φ : ComplexVector n → Pt X) (hΦ : IsLocalBiholomorphism Φ r) (h0 : Φ 0 ∈ K)
    (hlo : ∀ z ∈ ball (0 : ComplexVector n) r,
      HermLE ((c : ℂ) • (1 : Herm n)) (pullbackMat X.metric.form Φ z))
    (a : X.manifold.Carrier) (σ : ComplexVector n → ComplexVector n)
    (hW : ball (chartPt a (Φ 0)) δ ⊆ chartTarget a)
    (hmetric : ∀ w ∈ ball (chartPt a (Φ 0)) δ,
      HermLE ((d : ℂ) • (1 : Herm n)) (hMat X.metric.form a w) ∧
      HermLE (hMat X.metric.form a w) ((U : ℂ) • (1 : Herm n)))
    (hσ0 : σ (chartPt a (Φ 0)) = 0)
    (hσ : ContDiffOn ℂ ∞ σ (ball (chartPt a (Φ 0)) δ))
    (hσmem : MapsTo σ (ball (chartPt a (Φ 0)) δ) (ball 0 (r / 2)))
    (hright : ∀ w ∈ ball (chartPt a (Φ 0)) δ, Φ (σ w) = chartInv a w)
    (hO : IsOpen (σ '' ball (chartPt a (Φ 0)) δ))
    (hθσ : ∀ w ∈ ball (chartPt a (Φ 0)) δ, ShortLift.sheetCoordinates Φ a (σ w) = w)
    (hσθ : ∀ z ∈ σ '' ball (chartPt a (Φ 0)) δ, σ (ShortLift.sheetCoordinates Φ a z) = z)
    (hσdist : ∀ w ∈ ball (chartPt a (Φ 0)) δ,
      inducedDistance (chartExtendedField hn X Φ r hr hΦ) (0 : ComplexVector n) (σ w) ≤
        L * ‖w - chartPt a (Φ 0)‖)
    (α β : Covector n)
    (hαunit : dualNormMat (pullbackMat X.metric.form Φ 0) (covectorVector α) = 1)
    (hβunit : dualNormMat (pullbackMat X.metric.form Φ 0) (covectorVector β) = 1) :
    let k := (Cp / d + 1) / (κ / 2)
    let B := ((2 : ℝ) ^ n * (U * δs ^ 2) * (G ^ 2 / d)) *
      (volume : Measure (ComplexVector n)).real (closedBall 0 (r / 4))
    ∃ f h : ComplexVector n → ℂ, ∃ ψ : ComplexVector n → ℝ,
      Continuous f ∧ Differentiable ℂ h ∧ Continuous ψ ∧ fderiv ℂ h 0 = β ∧
      (∀ z, ‖f z‖ ≤ Real.sqrt U * δs) ∧
      (∀ z ∈ ball (0 : ComplexVector n) (r / 4),
        ψ z ≤ k * (chartLogBound c (covectorVector α) + 3)) ∧
      (∫⁻ z, ENNReal.ofReal (‖f z - h z‖ ^ 2 * Real.exp (-ψ z))
        ∂(volume : Measure (ComplexVector n))) ≤ ENNReal.ofReal B := by
  let w0 := chartPt a (Φ 0)
  let W := ball w0 δ
  let O := σ '' W
  let θ := ShortLift.sheetCoordinates Φ a
  let ks := chartExtendedField hn X Φ r hr hΦ
  let H := fun z : ComplexVector n => gMat ks z
  let Ht := hMat X.metric.form a
  let k := (Cp / d + 1) / (κ / 2)
  let B := ((2 : ℝ) ^ n * (U * δs ^ 2) * (G ^ 2 / d)) *
    (volume : Measure (ComplexVector n)).real (closedBall 0 (r / 4))
  have hks : MetricSmooth ks := chartExtendedField_metricSmooth hn X Φ r hr hΦ
  have hw0 : w0 ∈ W := mem_ball_self hδ
  have h0O : (0 : ComplexVector n) ∈ O := ⟨w0, hw0, hσ0⟩
  have hθ0 : θ 0 = w0 := by
    have hs : σ w0 = 0 := hσ0
    have ht : θ (σ w0) = w0 := hθσ w0 hw0
    rwa [hs] at ht
  have hσO : MapsTo σ W O := fun w hw => mem_image_of_mem σ hw
  have hθW : MapsTo θ O W := by
    rintro z ⟨w, hw, rfl⟩
    change ShortLift.sheetCoordinates Φ a (σ w) ∈ W
    rw [hθσ w hw]
    exact hw
  have hσr : MapsTo σ W (ball (0 : ComplexVector n) r) :=
    hσmem.mono_right (ball_subset_ball (by linarith))
  have hθ : ContDiffOn ℂ ∞ θ O := sheet_coordinates_holomorphic Φ r hΦ a W hW σ hσr hright
  have hθd : DifferentiableAt ℂ θ 0 := (hθ.contDiffAt (hO.mem_nhds h0O)).differentiableAt (by simp)
  have hsub : closedBall w0 δs ⊆ W := closedBall_subset_ball hδsδ
  have hHp (z : ComplexVector n) : (H z).PosDef := chartExtendedField_gMat_posDef hn X Φ r hr hΦ z
  have hgeom (z : ComplexVector n) (hz : z ∈ O) :=
    chart_sheet_point_metric hn X Φ r hr hΦ a W hW σ hσmem hright z hz
  have hcong (z : ComplexVector n) (hz : z ∈ O) :
      H z = (linearMatrix (fderiv ℂ θ z))ᴴ * Ht (θ z) * linearMatrix (fderiv ℂ θ z) :=
    (hgeom z hz).2.2
  have hHs0 : H 0 = pullbackMat X.metric.form Φ 0 :=
    chartExtendedField_gMat_inner hn X Φ r hr hΦ 0 (mem_closedBall_self (by positivity))
  obtain ⟨η, hηcomp, hηunit, hηnorm⟩ := exists_sheet_normalized_covector O W hO isOpen_ball
    h0O σ θ w0 hw0 hσ hθ hθ0 hσθ (pullbackMat X.metric.form Φ 0) (Ht w0)
    (by
      have HP : (Ht (θ 0)).PosDef := (hgeom 0 h0O).2.1
      rwa [hθ0] at HP) U hU (hmetric w0 hw0).2
    (by rw [← hHs0]; simpa only [hθ0] using hcong 0 h0O) β hβunit
  have hξ : covectorVector α ≠ 0 := by
    intro he
    have H0 := hαunit
    rw [he] at H0
    simp [dualNormMat] at H0
  obtain ⟨F, hF, hFp, hFu, hFT⟩ := exists_sheet_global_weight hn X Φ r c ρ ε hr hc hρ hΦ hlo
    hsmall hρε K K' h0 hfence κ hκ hcurv σ w0 δs δ L hδsδ hL.le hLδs
    hσ.continuousOn hσdist (covectorVector α) hξ hαunit
  have hD (z : ComplexVector n) (hz : z ∈ O) (v : ComplexVector n) :
      d * ‖fderiv ℂ θ z v‖ ^ 2 ≤ ellipsoidQuadratic (H z) v :=
    differential_quadratic_lower _ _ _ d (hcong z hz) (hmetric (θ z) (hθW hz)).1 v
  have hδps : δp ≤ δs := by linarith only [hsep, hδs]
  obtain ⟨hk, hφ, hpm, hp⟩ := sheet_weighted_poles O W hO σ θ hσ.continuousOn hσO hσθ hθ
    δp δs hδp hδps (n + 1) w0 hsub Cp d (κ / 2) hCp hd (by positivity)
    (hPole w0) H hHp hD F hF hFp (fun z hz => (hFT z hz).2)
  let p := sheetPole O θ δp hδp (n + 1) w0
  let φ := fun z => k * F z
  let f := sheetSeed O θ δs hδs η w0
  have hf := sheetSeed_smooth_compact O W hO σ θ hσ.continuousOn hσO hσθ
    (hθ.restrict_scalars ℝ) δs hδs η w0 hsub
  have hTsource : σ '' closedBall w0 δs ⊆ closedBall (0 : ComplexVector n) (r / 4) := by
    rintro z ⟨w, hw, rfl⟩
    have hdw := hσdist w (hsub hw)
    have hnormw : ‖w - w0‖ ≤ δs := by simpa only [mem_closedBall, dist_eq_norm] using hw
    have hdist : inducedDistance ks (0 : ComplexVector n) (σ w) ≤ ρ :=
      (hdw.trans (mul_le_mul_of_nonneg_left hnormw hL.le)).trans hLδs.le
    have HE := euclidean_dist_le_field_distance hn ks hks (min c 1) (lt_min hc zero_lt_one)
      (chartExtendedField_lower hn X Φ r c hr hΦ hlo) (0 : ComplexVector n) (σ w)
    rw [dist_zero_left] at HE
    rw [mem_closedBall, dist_zero_right]
    have Hmul := mul_le_mul_of_nonneg_left hdist (Real.sqrt_nonneg ((min c 1)⁻¹))
    nlinarith only [HE, Hmul, hsmall, hr]
  have hφT (z : ComplexVector n) (hz : z ∈ σ '' closedBall w0 δs) : 0 ≤ φ z :=
    mul_nonneg hk.le (hFT z hz).1
  have hsource := sheetSeed_source_integral_bound hn O W hO σ θ hσ.continuousOn hσO hσθ hθ hθW
    δs δp hδs hδp hsep η w0 hsub (r / 4) d U G (by positivity) hd hU.le hG hηnorm hcut
    hTsource Ht H (fun w hw => by
      exact Yau.LeafProofs.L12Aux.hMat_posDef X.metric.form a w (hW hw))
    (fun w hw => (hmetric w hw).1) (fun z hz => (hgeom z hz).1) hcong φ (n + 1) hφT
    (fun j => (hp j).2.2.2.1) (fun j => (hp j).2.2.2.2)
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  obtain ⟨h, hh, hb⟩ := exists_scalar_common_entire_solution hn f hf.1 hf.2.1 φ hφ
    p (fun j => (hp j).1) (fun j => (hp j).2.1) (fun j => (hp j).2.2.1)
    hpm (fun j => (hp j).2.2.2.1) B hB hsource
  obtain ⟨R0, hR0, hR0O, hθlocal, hθNZ, hflocal, hplocal⟩ :=
    exists_sheet_seed_pole_neighborhood O hO h0O σ θ hθ w0 hθ0 hσ0 hσθ
      δs δp hδs hδp hδps η
  have hjets := CorrectionJets.correction_jets_of_coordinate_poles hn f h
    (fun z => θ z - w0) φ p R0 hR0 hflocal hh hθlocal (by rw [hθ0, sub_self])
    hθNZ hφ.continuous.continuousOn
    (((n + 1 : ℕ) : ℝ) * Real.log (1 + δp ^ 2)) hplocal B hb
  have hseedjet := sheetSeed_zero_and_derivative O hO h0O θ hθd δs hδs η w0 hθ0
  refine ⟨f, h, (fun z => φ z + p 0 z), hf.1.continuous, hh,
    hφ.continuous.add (hp 0).1.continuous, ?_, ?_, ?_, hb 0⟩
  · exact hjets.2.trans (hseedjet.2.trans hηcomp)
  · intro z
    exact (sheetSeed_norm_le O θ δs hδs η w0 z).trans
      (mul_le_mul_of_nonneg_right hηnorm hδs.le)
  · intro z hz
    have H := mul_le_mul_of_nonneg_left (hFu z hz) hk.le
    have Hp := sheetPole_nonpos O θ δp hδp (n + 1) w0 0 z
    change k * F z + p 0 z ≤ k * (chartLogBound c (covectorVector α) + 3)
    change k * F z ≤ k * (chartLogBound c (covectorVector α) + 3) at H
    change p 0 z ≤ 0 at Hp
    linarith only [H, Hp]

end Yau.Proofs.C03Aux
