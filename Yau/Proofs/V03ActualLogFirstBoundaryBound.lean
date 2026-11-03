import Yau.Proofs.V03LogFirstProductBound
import Yau.Proofs.V03LogFieldContractions
import Yau.Proofs.V03BoundaryRealPart

/-! The genuine first real logarithmic jets satisfy a uniform original
boundary-seminorm estimate in every unit parameter direction. -/

open scoped Topology ContDiff Matrix

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

theorem actualLogFirstJet_uniform_boundaryDSq {n q : ℕ} {X : KahlerManifold n}
    {d : VariationData X q} (hd : VariationSetup d) (j a : ℕ) (ha : 4 ≤ a)
    (L : ℝ) (hL : 0 ≤ L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (F : VariationDisc X) (E : ℂ → CotangentMatrix n)
      (l : ℂ → CotangentIndex n → ℂ) (h α : ℂ → ℂ)
      (fz : ℂ → ℂ → CotangentPoint X.manifold) (R : ℝ),
      AdmissibleVariationDisc d j F → NormalizedDiscFrame d.G F.f E → HolomorphicColumn l →
      (∀ ζ ∈ Metric.closedBall (0 : ℂ) 1, ∑ i, ‖l ζ i‖ ^ 2 ≤ L ^ 2) →
      RealizesFirstField d j a F E l h α fz R → ∀ v : ℂ, ‖v‖ ≤ 1 →
      boundaryDSq (fun θ (_ : Unit) => realParameterDerivative
        (fun p : ℂ × ℝ => (logTrace d j (fz p.1) p.2 : ℂ)) v (0, θ)) ≤
        ENNReal.ofReal C *
          (1 + variationEnergy d j F + boundaryDSq (fun θ => l (circlePoint θ))) := by
  obtain ⟨C, hC, hprod⟩ := logFirstProduct_uniform_boundaryDSq hd j a ha L hL
  refine ⟨4 * C, mul_nonneg (by norm_num) hC,
    fun F E l h α fz R hF hE hl hlL hR v hv => ?_⟩
  let u : ℝ → ℂ := fun θ => normalizedVelocityScalar d j a F h α θ *
    (ambientLogCovector d j a (F.f (circlePoint θ)) ⬝ᵥ boundaryColumnField d F E l θ)
  have hAc (b : Fin q) : Continuous (fun θ => ambientLogCovector d j a (F.f (circlePoint θ)) b) :=
    cotangentCoefficient_trace_continuous hd
      (b := fun y => ambientLogCovector d j a y b)
      (fun x => ambientLogCovector_chart_entry_contDiffOn hd j a ha x b) hF
  have hWc := boundaryColumnField_continuous hd F E hE l hl
  have huc : Continuous u := (normalizedVelocityScalar_continuous hd j a F hF E l h α fz R hR).mul
    (continuous_finsetSum _ (fun b _ => (hAc b).mul (hWc b)))
  have hup : Function.Periodic u (2 * Real.pi) :=
    circleTrace_periodic (fun ζ => α ζ * (h ζ / (wallPower d j a (F.f ζ) : ℂ)) *
      (ambientLogCovector d j a (F.f ζ) ⬝ᵥ (ambientFrame d.G F.f E ζ *ᵥ l ζ)))
  have heq : (fun θ (_ : Unit) => realParameterDerivative
      (fun p : ℂ × ℝ => (logTrace d j (fz p.1) p.2 : ℂ)) v (0, θ)) =
      (fun θ (_ : Unit) => ((2 * (v * u θ).re : ℝ) : ℂ)) := by
    funext θ _
    simpa only [u, mul_assoc] using realized_logFirstJet_cleared hd j a ha F hF E l h α fz R hR v θ
  rw [heq]
  calc
    _ ≤ 4 * boundaryDSq (fun θ (_ : Unit) => u θ) := boundaryDSq_two_re_mul_le huc hup v hv
    _ ≤ 4 * (ENNReal.ofReal C *
        (1 + variationEnergy d j F + boundaryDSq (fun θ => l (circlePoint θ)))) := by
      gcongr
      exact hprod F E l h α fz R hF hE hl hlL hR
    _ = _ := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
      norm_num only [ENNReal.ofReal_ofNat]
      ring

end Yau.Blueprint.V03Proof
