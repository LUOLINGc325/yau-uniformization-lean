import Yau.Proofs.P06OneOneEnergyProjection
import Yau.Proofs.P06HodgeCoreClipping

noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace

namespace Yau.NodeProofs.P06Aux
open Yau Yau.LeafProofs.L03
variable {n : ℕ} {M : ComplexManifold n}

theorem hodgeEnergyCore_value (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A : RealForm M 2)
    (hA : SmoothRealForm A) (hcA : CompactlySupportedRealForm A) :
    hodgeEnergyValue g μ hμ (hodgeEnergyCore g μ hμ A hA hcA) =
      realizeActualForm g μ A (smooth_compactlySupported_l2RealForm g μ hμ A hA hcA) := rfl

/-- A pointwise L² contraction with a genuine compact-core q estimate
extends to the same original closed d/δ domain. All approximation data are
constructed from the actual typed energy vector. -/
theorem hodgeEnergy_raw_map_of_core_contraction (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (hk : IsKahler g)
    (P : RealForm M 2 → RealForm M 2)
    (hPL2 : ∀ A, L2RealForm g.form μ A → RealOneOne A → L2RealForm g.form μ (P A))
    (hPNorm : ∀ A B, RealOneOne A → RealOneOne B → ∀ x,
      formNormSq g.form (P A - P B) x ≤ formNormSq g.form (A - B) x)
    (hcore : ∀ (A : RealForm M 2) (hA : SmoothRealForm A)
      (hcA : CompactlySupportedRealForm A) (h11 : RealOneOne A),
      ∃ v : HodgeEnergySpace g μ hμ,
        hodgeEnergyValue g μ hμ v = realizeActualForm g μ (P A)
          (hPL2 A (smooth_compactlySupported_l2RealForm g μ hμ A hA hcA) h11) ∧
        hodgeEnergy g μ hμ v ≤ hodgeEnergy g μ hμ (hodgeEnergyCore g μ hμ A hA hcA))
    (u : HodgeEnergySpace g μ hμ) (A : RealForm M 2)
    (hA : L2RealForm g.form μ A) (h11 : RealOneOne A)
    (hu : hodgeEnergyValue g μ hμ u = realizeActualForm g μ A hA) :
    ∃ v : HodgeEnergySpace g μ hμ,
      hodgeEnergyValue g μ hμ v = realizeActualForm g μ (P A) (hPL2 A hA h11) ∧
        hodgeEnergy g μ hμ v ≤ hodgeEnergy g μ hμ u := by
  have hfixed : oneOneProjectionHilbert g μ (hodgeEnergyValue g μ hμ u) = hodgeEnergyValue g μ hμ u := by
    rw [hu, oneOneProjectionHilbert_realize]
    apply realizeActualForm_congr
    exact P06Weitzenbock.oneOneProjection_fixed A h11
  obtain ⟨As, hs, hc, htypes, ht⟩ := hodgeEnergyCore_oneOne_approximation g μ hμ hk u hfixed
  have hAs (j : ℕ) : L2RealForm g.form μ (As j) := smooth_compactlySupported_l2RealForm g μ hμ _ (hs j) (hc j)
  choose w hw hq using (fun j => hcore (As j) (hs j) (hc j) (htypes j))
  have hJ := (hodgeEnergyValue g μ hμ).continuous.continuousAt.tendsto.comp ht
  rw [hu] at hJ
  have hraw : Tendsto (fun j => formL2DistanceSq g.form μ (As j) A) atTop (𝓝 0) := by
    apply (tendsto_realizeL2Form_iff g μ (fun j => L2FormSpace.ofSection (As j) (hAs j))
      (L2FormSpace.ofSection A hA)).mp
    simpa only [Function.comp_def, hodgeEnergyCore_value, realizeActualForm] using hJ
  have hdist (j : ℕ) : formL2DistanceSq g.form μ (P (As j)) (P A) ≤ formL2DistanceSq g.form μ (As j) A := by
    apply lintegral_mono
    intro x
    exact ENNReal.ofReal_le_ofReal (hPNorm (As j) A (htypes j) h11 x)
  have hPraw : Tendsto (fun j => formL2DistanceSq g.form μ (P (As j)) (P A)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hraw (fun _ => bot_le) hdist
  have hPstrong := (tendsto_realizeL2Form_iff g μ
    (fun j => L2FormSpace.ofSection (P (As j)) (hPL2 (As j) (hAs j) (htypes j)))
    (L2FormSpace.ofSection (P A) (hPL2 A hA h11))).mpr hPraw
  have hstrong : Tendsto (fun j => hodgeEnergyValue g μ hμ (w j)) atTop
      (𝓝 (realizeActualForm g μ (P A) (hPL2 A hA h11))) := by
    simpa only [hw, realizeActualForm] using hPstrong
  have henergy : Tendsto (fun j => hodgeEnergy g μ hμ
      (hodgeEnergyCore g μ hμ (As j) (hs j) (hc j))) atTop (𝓝 (hodgeEnergy g μ hμ u)) :=
    (((hodgeEnergyExterior g μ hμ).continuous.continuousAt.tendsto.comp ht).norm.pow 2).add
      (((hodgeEnergyLower g μ hμ).continuous.continuousAt.tendsto.comp ht).norm.pow 2)
  exact hodgeEnergy_strong_image_limit g μ hμ w _ _ _ hstrong hq henergy

end Yau.NodeProofs.P06Aux
