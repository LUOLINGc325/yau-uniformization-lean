import Yau.Proofs.C03ChartConstruction
import Yau.Proofs.C03Rayleigh
import Yau.Proofs.C03ScalarEstimate
import Yau.Proofs.C03LogGrowth

/-! The paper's original static-distortion estimate, with one positive
constant chosen before the map and with the complete frozen quantifiers. -/

noncomputable section
open Set Metric MeasureTheory
open scoped Topology ContDiff Manifold Matrix ComplexOrder
namespace Yau.Proofs.C03Aux
open Yau Yau.Blueprint Yau.BlueprintContracts Yau.LeafProofs L12Aux
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

theorem static_distortion_proved (hn : 1 ≤ n) (X : KahlerManifold n) : StaticDistortion X := by
  intro r c hr hc K hK
  obtain ⟨K', ε, κ, d, U, L, ρ, δ, hε, hκ, hd, hU, hL, hρ, hδ,
    hρε, hsmall, hLδ, hfence, hcurv, hsheets⟩ := exists_uniform_source_sheets hn X r c hr hc K hK
  let δs := δ / 2
  let δp := δs / 4
  have hδs : 0 < δs := by dsimp only [δs]; positivity
  have hδp : 0 < δp := by dsimp only [δp]; positivity
  have hδsδ : δs < δ := by dsimp only [δs]; linarith
  have hsep : δp < δs / 2 := by dsimp only [δp]; linarith
  have hLδs : L * δs < ρ := by
    have H := mul_lt_mul_of_pos_left hδsδ hL
    exact H.trans hLδ
  obtain ⟨Cp, hCp, hPole⟩ := TargetPole.exists_translatedPole_uniform_levi_lower (n := n) δp hδp (n + 1)
  obtain ⟨G, hG, hcut⟩ := exists_seedCutoffDbar_bound (n := n) δs hδs
  let k := (Cp / d + 1) / (κ / 2)
  have hk : 0 < k := by dsimp only [k]; positivity
  let B := ((2 : ℝ) ^ n * (U * δs ^ 2) * (G ^ 2 / d)) *
    (volume : Measure (ComplexVector n)).real (closedBall 0 (r / 4))
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  let S := Real.sqrt U * δs
  have hS : 0 ≤ S := by dsimp only [S]; positivity
  let V := (volume : Measure (ComplexVector n)).real (closedBall 0 (r / 8))
  have hV : 0 ≤ V := measureReal_nonneg
  let M0 := max 0 (-Real.log (min c 1))
  obtain ⟨D, hD, hDall⟩ := ScalarEstimate.exists_weighted_derivative_bound (n := n) (r / 8) (by positivity)
  obtain ⟨P, hP, hGrowth⟩ := exists_log_weight_power_bound D S V B k M0 hD.le hV hB hk
  obtain ⟨C, hC, hAbsorb⟩ := absorb_coefficient_and_exponent P k
  refine ⟨C, hC, ?_⟩
  intro Φ hΦ h0 hlo
  have hH0 : (pullbackMat X.metric.form Φ 0).PosDef := by
    have H := chartExtendedField_gMat_posDef hn X Φ r hr hΦ (0 : ComplexVector n)
    rwa [chartExtendedField_gMat_inner hn X Φ r hr hΦ 0 (mem_closedBall_self (by positivity))] at H
  obtain ⟨α, β, hαnorm, hβnorm, hαunit, hβunit⟩ :=
    Rayleigh.exists_normalized_extreme_covectors hn (pullbackMat X.metric.form Φ 0) hH0
  obtain ⟨a, σ, hW, hmetric, hσ0, hσ, hσmem, hright, hO, hθσ, hσθ, hσdist⟩ :=
    hsheets Φ hΦ h0 hlo
  obtain ⟨f, h, ψ, hf, hh, hψ, hjet, hfS, hψupper, hb⟩ :=
    chart_scalar_estimate_data hn X r c ρ ε κ d U L δ δs δp Cp G hr hc hρ hκ hd hU hL
      hδ hδs hδp hδsδ hsep hLδs hCp hG.le hsmall hρε K K' hfence hcurv hPole hcut
      Φ hΦ h0 hlo a σ hW hmetric hσ0 hσ hσmem hright hO hθσ hσθ hσdist α β hαunit hβunit
  let A := Real.sqrt (relMinEigenvalue (1 : Herm n) (pullbackMat X.metric.form Φ 0))
  have hA : 0 ≤ A := Real.sqrt_nonneg _
  have hψM : ∀ z ∈ closedBall (0 : ComplexVector n) (r / 8),
      ψ z ≤ k * (M0 + 2 * Real.log (1 + A) + 3) := by
    intro z hz
    have hzD : z ∈ ball (0 : ComplexVector n) (r / 4) := closedBall_subset_ball (by linarith) hz
    have H := hψupper z hzD
    simpa only [chartLogBound, covectorVector_norm, hαnorm, M0, A] using H
  have H := hDall f h ψ (k * (M0 + 2 * Real.log (1 + A) + 3)) S B
    hf hh hψ hS hB (fun z _ => hfS z) hψM hb
  rw [hjet, hβnorm] at H
  apply hAbsorb A _ hA
  exact H.trans (hGrowth A hA)

/-- Exact original conditional endpoint; the geometric lower bound in the
frozen static-distortion hypothesis supplies the needed short lifts. -/
theorem C03_contract_proved (_hC02 : C02_contract) : C03_contract := by
  intro n X
  exact static_distortion_proved (manifold_dimension_pos X.manifold) X

/-- Direct original contract, obtained from the already proved static estimate. -/
theorem C03_contract_unconditional : C03_contract := by
  intro n X
  exact static_distortion_proved (manifold_dimension_pos X.manifold) X

end Yau.Proofs.C03Aux
