import Yau.LeafProofs.L16DeGiorgiTruncation

open MeasureTheory Filter Set
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius

noncomputable section

namespace Yau.F04Proof

open Yau.Parabolic Yau.LeafProofs.L16Aux

/-- The genuine finite-time cutoff estimate on an arbitrary open spatial domain.
The bottom time remains strictly inside the classical equation cylinder. -/
theorem cutoff_truncation_caccioppoli {n : ℕ} {O : Set (Space n)} (hO : IsOpen O)
    {l r a b ν L D F : ℝ} (hla : l < a) (hab : a < b) (hbr : b ≤ r)
    (hν : 0 < ν) (hD : 0 ≤ D) (hF : 0 ≤ F)
    {A : Point n → Mat n} {c : Point n → Yau.RIdx n → ℝ} {f u ζ : Point n → ℝ}
    (hf : DGClassicalFields (O ×ˢ Ioo l r) A c f u)
    (hpde : ClassicalDivEq (O ×ˢ Ioo l r) A c f u)
    (hb : DGUniformBounds (O ×ˢ Ioo l r) A c f ν L D F)
    (hu : ContinuousOn u (O ×ˢ Icc a b)) (hζ : DGSpatialCutoff O a b ζ)
    (σ k : ℝ) (hσ : DGSign σ) :
    Integrable (dgTruncationEnergyDensity σ k u ζ) (productVolume O (Ioo a b)) ∧
      ν * dgCylinderIntegral O a b (dgTruncationEnergyDensity σ k u ζ) ≤
        (2 + 8 * L ^ 2 / ν + 2 * D ^ 2 / ν) *
          dgCylinderIntegral O a b (dgTruncationCutoffError σ k u ζ) +
        2 * F * dgCylinderIntegral O a b (dgTruncationForcingDensity σ k u ζ) +
        dgSliceEnergy O (dgTruncation σ k u) ζ a := by
  let H := dgTruncationEnergyDensity σ k u ζ
  let X := dgTruncationCutoffError σ k u ζ
  let Q := dgTruncationForcingDensity σ k u ζ
  let S := dgSliceEnergy O (dgTruncation σ k u) ζ
  let K0 := 2 + 8 * L ^ 2 / ν + 2 * D ^ 2 / ν
  let M := K0 * dgCylinderIntegral O a b X +
    2 * F * dgCylinderIntegral O a b Q + S a
  have hX0 (z : Point n) : 0 ≤ X z := by
    dsimp only [X, dgTruncationCutoffError]
    have := dgGradientSq_nonneg (dgGradient ζ z)
    positivity
  have hQ0 (z : Point n) : 0 ≤ Q z :=
    mul_nonneg (dgPositivePart_nonneg _) (sq_nonneg _)
  have hS0 (t : ℝ) : 0 ≤ S t :=
    integral_nonneg (fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hH0 (z : Point n) : 0 ≤ H z :=
    mul_nonneg (dgGradientSq_nonneg _) (sq_nonneg _)
  have hM0 : 0 ≤ M := by
    have hx : 0 ≤ dgCylinderIntegral O a b X := integral_nonneg hX0
    have hq : 0 ≤ dgCylinderIntegral O a b Q := integral_nonneg hQ0
    have hs := hS0 a
    have hK0 : 0 ≤ K0 := by dsimp only [K0]; positivity
    exact add_nonneg (add_nonneg (mul_nonneg hK0 hx) (mul_nonneg (by positivity) hq)) hs
  have hpref (τ : ℝ) (hτ : τ ∈ Ioo a b) :
      S τ + ν * dgCylinderIntegral O a τ H ≤ M :=
    dgTruncation_prefix_estimate hO hla hτ.1 hτ.2 hbr hν hD hF hf hpde hb hu hζ hσ
  have hVU : O ×ˢ Ioo a b ⊆ O ×ˢ Ioo l r :=
    fun z hz => ⟨hz.1, hla.trans hz.2.1, hz.2.2.trans_le hbr⟩
  have hHmeas : AEStronglyMeasurable H (productVolume O (Ioo a b)) := by
    rw [dg_productVolume_eq_restrict]
    exact dgTruncationEnergyDensity_aestronglyMeasurable
      (hO.prod isOpen_Ioo) (hf.2.2.2.mono hVU) hζ.1 σ k
  have hfull := dg_fullSlab_integrable_of_prefix_bounds hO hab
    (div_nonneg hM0 hν.le) hHmeas (.of_forall hH0) (fun τ hτ => by
      refine ⟨dgTruncation_energy_integrable_before_top hO hla hτ.1 hτ.2 hbr hf.2.2.2 hζ, ?_⟩
      apply (le_div_iff₀ hν).mpr
      have hh := hpref τ hτ
      have hs := hS0 τ
      nlinarith only [hh, hs])
  refine ⟨hfull.1, ?_⟩
  change ν * dgCylinderIntegral O a b H ≤ M
  nlinarith only [(le_div_iff₀ hν).mp hfull.2]

end Yau.F04Proof
