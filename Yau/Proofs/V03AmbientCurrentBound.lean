import Yau.Proofs.V03ExpandedCurrentControl
import Yau.Proofs.V03RealizedCurrentExpansion
import Yau.Proofs.V03FiniteCurrentIntegral
import Yau.Proofs.V03RealizedAreaCurrents

/-! The actual intrinsic quadratic area current has a single uniform
bound before every original realization, by its genuine finite signed expansion. -/

open scoped Topology ContDiff Matrix
open MeasureTheory

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

theorem ambientQuadraticDiscCurrent_uniform_bound {n q : ℕ} {X : KahlerManifold n}
    {d : VariationData X q} (hd : VariationSetup d) (j a : ℕ)
    {B : CotangentPoint X.manifold → Matrix (Fin q) (Fin q) ℂ}
    (hB : ∀ x b c, ContDiffOn ℝ ∞ (fun z => B (cotangentChartInv x z) b c) (cotangentTarget x))
    (L : ℝ) (hL : 0 ≤ L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (F : VariationDisc X) (E : ℂ → CotangentMatrix n)
      (l : ℂ → CotangentIndex n → ℂ) (h α : ℂ → ℂ)
      (fz : ℂ → ℂ → CotangentPoint X.manifold) (R : ℝ),
      AdmissibleVariationDisc d j F → NormalizedDiscFrame d.G F.f E → HolomorphicColumn l →
      (∀ ζ ∈ Metric.closedBall (0 : ℂ) 1, ∑ i, ‖l ζ i‖ ^ 2 ≤ L ^ 2) →
      RealizesFirstField d j a F E l h α fz R →
      |ambientQuadraticDiscCurrent B F.f (ambientVelocity d F E l h α)| ≤
        C * (1 + (variationEnergy d j F).toReal +
          (boundaryDSq (fun θ => l (circlePoint θ))).toReal) := by
  obtain ⟨C, hC, hAtoms⟩ := realizedExpandedAtom_uniform_bound hd j a hB L hL
  let N : ℝ := Fintype.card (CurrentExpansionIndex q)
  have hN : 0 ≤ N := by dsimp only [N]; positivity
  refine ⟨N * C, mul_nonneg hN hC, fun F E l h α fz R hF hE hl hlL hR => ?_⟩
  let A := realizedExpandedAtom d B F E l h α
  have hc (t : CurrentExpansionIndex q) : Continuous (A t) :=
    realizedExpandedAtom_continuous hd j a hB F hF E l h α fz R hR t
  have he (θ : ℝ) : closedRealGradient (fun ζ => 2 *
      (star (fun b => ambientVelocity d F E l h α ζ b) ⬝ᵥ
        (B (F.f ζ) *ᵥ fun b => ambientVelocity d F E l h α ζ b)).re)
      (circlePoint θ) (circlePoint θ) = 2 * ∑ t : CurrentExpansionIndex q, A t θ := by
    rw [sum_realizedExpandedAtom]
    exact realized_quadratic_radial_expansion hd j a hB F hF E l h α fz R hR θ
  have hi : ambientQuadraticDiscCurrent B F.f (ambientVelocity d F E l h α) =
      (1 / 2 : ℝ) * ∫ θ in (-Real.pi)..Real.pi, ∑ t : CurrentExpansionIndex q, A t θ := by
    unfold ambientQuadraticDiscCurrent
    rw [intervalIntegral.integral_congr (fun θ _ => he θ), intervalIntegral.integral_const_mul]
    ring
  have hb := abs_intervalIntegral_fintype_sum_le
    (fun t => (hc t).intervalIntegrable (-Real.pi) Real.pi)
    (hAtoms F E l h α fz R hF hE hl hlL hR)
  rw [hi, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  calc
    _ ≤ |∫ θ in (-Real.pi)..Real.pi, ∑ t : CurrentExpansionIndex q, A t θ| := by
      nlinarith [abs_nonneg (∫ θ in (-Real.pi)..Real.pi, ∑ t : CurrentExpansionIndex q, A t θ)]
    _ ≤ N * (C * (1 + (variationEnergy d j F).toReal +
        (boundaryDSq (fun θ => l (circlePoint θ))).toReal)) := hb
    _ = _ := by ring

end Yau.Blueprint.V03Proof
