import Yau.Proofs.V03AmbientCurrentBound

/-! Both original geometric area summands satisfy their full actual
mixed derivative estimates with one constant before every original realization. -/

open scoped Topology ContDiff Matrix

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

variable {n q : ℕ} {X : KahlerManifold n} {d : VariationData X q}

theorem actualBaseAreaEnergyDerivative (hd : VariationSetup d) (j a : ℕ) (L : ℝ) (hL : 0 ≤ L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (F : VariationDisc X) (E : ℂ → CotangentMatrix n)
      (l : ℂ → CotangentIndex n → ℂ) (h α : ℂ → ℂ)
      (fz : ℂ → ℂ → CotangentPoint X.manifold) (R : ℝ),
      AdmissibleVariationDisc d j F → NormalizedDiscFrame d.G F.f E → HolomorphicColumn l →
      (∀ ζ ∈ Metric.closedBall (0 : ℂ) 1, ∑ i, ‖l ζ i‖ ^ 2 ≤ L ^ 2) →
      RealizesFirstField d j a F E l h α fz R →
      |mixedReal (fun z => (discArea X.metric.form (fun ζ => (fz z ζ).1)).toReal)| ≤
        C * (1 + (variationEnergy d j F).toReal +
          (boundaryDSq (fun θ => l (circlePoint θ))).toReal) := by
  obtain ⟨C, hC, hb⟩ := ambientQuadraticDiscCurrent_uniform_bound hd j a
    (B := ambientBaseTensor d.G X.metric.form)
    (ambientBaseTensor_chart_entry_contDiffOn hd.2.2.2.2.1 X.metric) L hL
  refine ⟨C, hC, fun F E l h α fz R hF hE hl hlL hR => ?_⟩
  rw [realized_baseArea_mixed_current hd hR]
  exact hb F E l h α fz R hF hE hl hlL hR

theorem actualGaussAreaEnergyDerivative (hd : VariationSetup d) (j a : ℕ) (L : ℝ) (hL : 0 ≤ L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (F : VariationDisc X) (E : ℂ → CotangentMatrix n)
      (l : ℂ → CotangentIndex n → ℂ) (h α : ℂ → ℂ)
      (fz : ℂ → ℂ → CotangentPoint X.manifold) (R : ℝ),
      AdmissibleVariationDisc d j F → NormalizedDiscFrame d.G F.f E → HolomorphicColumn l →
      (∀ ζ ∈ Metric.closedBall (0 : ℂ) 1, ∑ i, ‖l ζ i‖ ^ 2 ≤ L ^ 2) →
      RealizesFirstField d j a F E l h α fz R →
      |mixedReal (fun z => gaussArea d.G (fz z))| ≤
        C * (1 + (variationEnergy d j F).toReal +
          (boundaryDSq (fun θ => l (circlePoint θ))).toReal) := by
  obtain ⟨C, hC, hb⟩ := ambientQuadraticDiscCurrent_uniform_bound hd j a
    (B := ambientGaussTensor d.G)
    (ambientGaussTensor_chart_entry_contDiffOn hd.2.2.2.2.1) L hL
  refine ⟨C, hC, fun F E l h α fz R hF hE hl hlL hR => ?_⟩
  rw [realized_gaussArea_mixed_current hd hR]
  exact hb F E l h α fz R hF hE hl hlL hR

end Yau.Blueprint.V03Proof
