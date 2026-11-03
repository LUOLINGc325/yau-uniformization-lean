import Yau.Proofs.V03LogMixedProductBound
import Yau.Proofs.V03ActualLogMixedCleared
import Yau.Proofs.V03BoundaryRealPart

/-! The genuine pointwise mixed logarithmic jet has one uniform
original boundary-seminorm bound before every realization. -/

open scoped Topology ContDiff Matrix

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

theorem actualLogMixedJet_uniform_boundaryDSq {n q : ℕ} {X : KahlerManifold n}
    {d : VariationData X q} (hd : VariationSetup d) (j a : ℕ) (ha : 4 ≤ a)
    (L : ℝ) (hL : 0 ≤ L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (F : VariationDisc X) (E : ℂ → CotangentMatrix n)
      (l : ℂ → CotangentIndex n → ℂ) (h α : ℂ → ℂ)
      (fz : ℂ → ℂ → CotangentPoint X.manifold) (R : ℝ),
      AdmissibleVariationDisc d j F → NormalizedDiscFrame d.G F.f E → HolomorphicColumn l →
      (∀ ζ ∈ Metric.closedBall (0 : ℂ) 1, ∑ i, ‖l ζ i‖ ^ 2 ≤ L ^ 2) →
      RealizesFirstField d j a F E l h α fz R →
      scalarDSq (fun θ => mixedReal (fun z => logTrace d j (fz z) θ)) ≤
        ENNReal.ofReal C *
          (1 + variationEnergy d j F + boundaryDSq (fun θ => l (circlePoint θ))) := by
  obtain ⟨C, hC, hprod⟩ := logMixedProduct_uniform_boundaryDSq hd j a ha L hL
  refine ⟨C, hC, fun F E l h α fz R hF hE hl hlL hR => ?_⟩
  let c := normalizedVelocityScalar d j a F h α
  let W := boundaryColumnField d F E l
  let B : ℝ → Matrix (Fin q) (Fin q) ℂ := fun θ => ambientLogTensor d j a (F.f (circlePoint θ))
  let u : ℝ → ℂ := fun θ => star (c θ) * c θ * (star (W θ) ⬝ᵥ (B θ *ᵥ W θ))
  have hc := normalizedVelocityScalar_continuous hd j a F hF E l h α fz R hR
  have hWc := boundaryColumnField_continuous hd F E hE l hl
  have hBc (b c : Fin q) : Continuous (fun θ => B θ b c) :=
    cotangentCoefficient_trace_continuous hd
      (b := fun y => ambientLogTensor d j a y b c)
      (fun x => ambientLogTensor_chart_entry_contDiffOn hd j a ha x b c) hF
  have hqc : Continuous (fun θ => star (W θ) ⬝ᵥ (B θ *ᵥ W θ)) := by
    simp_rw [quadraticForm_eq_sum]
    exact continuous_finsetSum _ (fun bc _ => ((hWc bc.1).star.mul (hBc bc.1 bc.2)).mul (hWc bc.2))
  have huc : Continuous u := (hc.star.mul hc).mul hqc
  have hup : Function.Periodic u (2 * Real.pi) := circleTrace_periodic (fun ζ =>
    star (α ζ * (h ζ / (wallPower d j a (F.f ζ) : ℂ))) *
      (α ζ * (h ζ / (wallPower d j a (F.f ζ) : ℂ))) *
        (star (ambientFrame d.G F.f E ζ *ᵥ l ζ) ⬝ᵥ
          (ambientLogTensor d j a (F.f ζ) *ᵥ (ambientFrame d.G F.f E ζ *ᵥ l ζ))))
  have heq : (fun θ => mixedReal (fun z => logTrace d j (fz z) θ)) = (fun θ => (u θ).re) := by
    funext θ
    exact realized_logMixedJet_cleared hd j a ha F hF E l h α fz R hR θ
  rw [heq]
  exact (boundaryDSq_real_part_le huc hup).trans (hprod F E l h α fz R hF hE hl hlL hR)

end Yau.Blueprint.V03Proof
