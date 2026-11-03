import Yau.Proofs.V04BoundaryRegularity
import Yau.Proofs.V04FactorBoundaryQuad

/-! Boundary averages use the actual continuous quadratic integrand.
The same caller-supplied inverse factor is used at every boundary point. -/

open scoped Matrix ComplexOrder Topology ContDiff
open MeasureTheory
noncomputable section
namespace Yau.Blueprint.V04Proof
open Yau Yau.Blueprint

variable {n q : ℕ} {X : KahlerManifold n}

theorem circleAverage_const_value (c : ℝ) : circleAverage (fun _ => c) = c := by
  unfold circleAverage
  rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  have hp : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  rw [← mul_assoc, inv_mul_cancel₀ hp, one_mul]

theorem circleAverage_le_of_continuous {f : ℝ → ℝ} (hf : Continuous f) {c : ℝ}
    (hfc : ∀ θ, f θ ≤ c) : circleAverage f ≤ c := by
  rw [← circleAverage_const_value c]
  apply mul_le_mul_of_nonneg_left
    (intervalIntegral.integral_mono_on (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
      (hf.intervalIntegrable _ _) intervalIntegrable_const (fun θ _ => hfc θ))
  positivity

theorem quadValue_continuous {A : ℝ → CotangentMatrix n}
    {v : ℝ → CotangentIndex n → ℂ}
    (hA : ∀ i k, Continuous (fun θ => A θ i k))
    (hv : ∀ i, Continuous (fun θ => v θ i)) :
    Continuous (fun θ => quadValue (A θ) (v θ)) := by
  unfold quadValue
  apply Complex.continuous_re.comp
  simp only [dotProduct, Matrix.mulVec]
  apply continuous_finset_sum
  intro i _
  apply (hv i).star.mul
  apply continuous_finset_sum
  intro k _
  exact (hA i k).mul (hv k)

theorem spectralFactor_unit_column_boundary_average {d : VariationData X q}
    (hd : VariationSetup d) {j a : ℕ} (ha : 4 ≤ a) {δ : ℝ} (hδ : 0 < δ)
    {F : VariationDisc X} (hF : AdmissibleVariationDisc d j F)
    {E H Hinv : ℂ → CotangentMatrix n} (hE : NormalizedDiscFrame d.G F.f E)
    (hH : SpectralFactorFor d j a δ F E H Hinv)
    (hT : ∀ θ, (boundarySymbol d j a F E (circlePoint θ)).IsHermitian)
    (v : EuclideanSpace ℂ (CotangentIndex n)) (hv : ‖v‖ ≤ 1) :
    circleAverage (fun θ => quadValue (boundarySymbol d j a F E (circlePoint θ))
      (Hinv (circlePoint θ) *ᵥ WithLp.ofLp v)) ≤ 1 := by
  apply circleAverage_le_of_continuous
  · apply quadValue_continuous
    · intro i k
      exact (boundarySymbol_trace_contDiff hd j a ha F hF E hE i k).continuous
    · intro i
      simp only [Matrix.mulVec, dotProduct]
      apply continuous_finset_sum
      intro k _
      exact (closedDisc_scalar_trace_contDiff (hH.1 i k).2).continuous.mul continuous_const
  · exact spectralFactor_unit_column_boundary_quad hδ hH hT v hv

end Yau.Blueprint.V04Proof
