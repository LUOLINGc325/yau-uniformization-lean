import Yau.Proofs.V02CramerLinear
import Yau.Proofs.V02SpanningCoefficientBounds
import Yau.Proofs.V03BoundaryColumnField

/-! All polynomial Cramer coefficients and the actual normalized frame
column have uniform boundary controls from the original full energy. -/

open scoped Topology ContDiff Manifold Matrix

noncomputable section
namespace Yau.Blueprint.V02Proof
open Yau Yau.Blueprint

variable {n q b : ℕ} {X : KahlerManifold n}

theorem spanningCramerCoefficient_uniform_boundary_control
    {d : VariationData X q} (hd : VariationSetup d) (j : ℕ) (E₀ : ℝ)
    {Z : Fin b → CotangentPoint X.manifold → CotangentIndex n → ℂ}
    (hZ : ∀ k x i, DifferentiableOn ℂ
      (fun z => (cotangentTransition (chartInv x z.1) x (cotangentChartInv x z) *ᵥ
        Z k (cotangentChartInv x z)) i) (cotangentTarget x)) :
    ∃ D M : ℝ, 0 ≤ D ∧ 0 ≤ M ∧ ∀ F : VariationDisc X,
      AdmissibleVariationDisc d j F → (variationEnergy d j F).toReal ≤ E₀ →
      ∀ (k : SpanningMinorIndex n q b) (i : Fin b) (a : Fin q),
      (∀ θ, ‖spanningCramerCoefficient d.G Z k i a (F.f (circlePoint θ))‖ ≤ M) ∧
      boundaryDSq (fun θ (_ : Unit) => spanningCramerCoefficient d.G Z k i a
        (F.f (circlePoint θ))) ≤ ENNReal.ofReal D := by
  let ι := SpanningMinorIndex n q b × Fin b × Fin q
  let B : ι → CotangentPoint X.manifold → ℂ := fun p =>
    spanningCramerCoefficient d.G Z p.1 p.2.1 p.2.2
  have hB (p : ι) (x : Pt X) :
      ContDiffOn ℝ ∞ (fun z => B p (cotangentChartInv x z)) (cotangentTarget x) :=
    (spanningCramerCoefficient_chart_contDiffOn hd.2.2.2.2.1.1 hZ p.1 p.2.1 p.2.2 x).restrict_scalars ℝ
  obtain ⟨D, M, hD, hM, hbound⟩ := finiteCoefficients_boundary_control_of_energy_bound hd j E₀ hB
  exact ⟨D, M, hD, hM, fun F hF hE k i a => hbound F hF hE (k, i, a)⟩

theorem boundaryColumnField_uniform_control_of_energy_bound
    {d : VariationData X q} (hd : VariationSetup d) (j : ℕ)
    (L : ℝ) (hL : 0 ≤ L) (E₀ D₀ : ℝ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (F : VariationDisc X) (E : ℂ → CotangentMatrix n)
      (l : ℂ → CotangentIndex n → ℂ),
      AdmissibleVariationDisc d j F → (variationEnergy d j F).toReal ≤ E₀ →
      NormalizedDiscFrame d.G F.f E → HolomorphicColumn l →
      (∀ ζ ∈ Metric.closedBall (0 : ℂ) 1, ∑ i, ‖l ζ i‖ ^ 2 ≤ L ^ 2) →
      boundaryDSq (fun θ => l (circlePoint θ)) ≤ ENNReal.ofReal (D₀ ^ 2) →
      (∀ θ a, ‖V03Proof.boundaryColumnField d F E l θ a‖ ≤ L) ∧
      boundaryDSq (V03Proof.boundaryColumnField d F E l) ≤ ENNReal.ofReal D := by
  obtain ⟨C, hC, hbound⟩ := V03Proof.boundaryColumnField_uniform_boundaryDSq hd j L hL
  let D : ℝ := C * (max E₀ 0 + D₀ ^ 2)
  refine ⟨D, by dsimp [D]; positivity, fun F E l hF hE hframe hl hlL hlD => ?_⟩
  have hEn : variationEnergy d j F ≤ ENNReal.ofReal (max E₀ 0) := by
    rw [← ENNReal.ofReal_toReal hF.2.2.2.2.2.2.2.2]
    exact ENNReal.ofReal_le_ofReal (hE.trans (le_max_left _ _))
  refine ⟨V03Proof.boundaryColumnField_norm_le F E hframe l hL hlL, ?_⟩
  have hs : variationEnergy d j F + boundaryDSq (fun θ => l (circlePoint θ)) ≤
      ENNReal.ofReal (max E₀ 0 + D₀ ^ 2) := by
    rw [ENNReal.ofReal_add (le_max_right _ _) (sq_nonneg _)]
    exact add_le_add hEn hlD
  exact (hbound F E l hframe hl hlL).trans (by
    dsimp only [D]
    rw [ENNReal.ofReal_mul hC]
    exact mul_le_mul_right hs (ENNReal.ofReal C))

end Yau.Blueprint.V02Proof
