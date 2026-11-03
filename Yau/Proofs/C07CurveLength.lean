import Yau.Proofs.C07CurveLengthMetric
import Yau.Proofs.C07CurveLengthMeasurable

open scoped Manifold Topology

noncomputable section

namespace Yau.Proofs.C07CurveLengthAux

open Yau Yau.Blueprint Set Filter MeasureTheory

variable {n : ℕ} {M : ComplexManifold n}

/-- Reinterpreting the same original curve in a smaller smooth metric
preserves integrability and gives the precise square-root length bound. -/
theorem curve_length_comparison {k₀ k₁ : HermitianField M} {x y : M.Carrier}
    (hk₁ : MetricSmooth k₁) (γ : IntegrableCurve k₀ x y) {A : ℝ} (hA : 0 ≤ A)
    (horder : ∀ t ∈ Icc (0 : ℝ) 1,
      HermLE (gMat k₁ (γ.1 t)) ((A : ℂ) • gMat k₀ (γ.1 t))) :
    IntegrableOn (curveSpeed k₁ γ.1) (Icc (0 : ℝ) 1) ∧
      curveLength k₁ γ.1 ≤ Real.sqrt A * curveLength k₀ γ.1 := by
  have hupper : IntegrableOn (fun t => Real.sqrt A * curveSpeed k₀ γ.1 t)
      (Icc (0 : ℝ) 1) := γ.2.const_mul _
  have hbound : curveSpeed k₁ γ.1 ≤ᵐ[volume.restrict (Icc (0 : ℝ) 1)]
      (fun t => Real.sqrt A * curveSpeed k₀ γ.1 t) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact curveSpeed_le_sqrt_mul γ.1 hA t (horder t ht)
  have hint : IntegrableOn (curveSpeed k₁ γ.1) (Icc (0 : ℝ) 1) := by
    apply hupper.mono' (curveSpeed_aestronglyMeasurable k₁ hk₁ γ.1)
    filter_upwards [hbound] with t ht
    rw [Real.norm_of_nonneg (show 0 ≤ curveSpeed k₁ γ.1 t from Real.sqrt_nonneg _)]
    exact ht
  refine ⟨hint, ?_⟩
  have h := integral_mono_ae hint hupper hbound
  simpa only [curveLength, integral_const_mul] using h

end Yau.Proofs.C07CurveLengthAux
