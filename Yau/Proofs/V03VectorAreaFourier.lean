import Yau.Proofs.V03VectorAreaSum
import Yau.Proofs.V03ScalarAreaFourier
import Yau.Proofs.V03ClockRadial
import Yau.Proofs.V03BoundaryVectorProduct

/-! Exact original Euclidean and clock area/Fourier normalizations,
including every finite-dimensional rank and the original closed circle. -/

open scoped Topology ContDiff

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

theorem normDiscArea_vector_eq_boundaryDSq {ι : Type*} [Fintype ι]
    {f : ℂ → EuclideanSpace ℂ ι} (hf : ContDiffOn ℂ ∞ f (Metric.closedBall (0 : ℂ) 1)) :
    normDiscArea f = ENNReal.ofReal (2 * Real.pi) * boundaryDSq (fun θ i => f (circlePoint θ) i) := by
  rw [normDiscArea_vector_eq_sum hf, boundaryDSq_eq_sum_singleton, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact normDiscArea_scalar_eq_boundaryDSq ((contDiffOn_piLp 2).mp hf i)

theorem boundaryDSq_vector_eq_inverse_area {ι : Type*} [Fintype ι]
    {f : ℂ → EuclideanSpace ℂ ι} (hf : ContDiffOn ℂ ∞ f (Metric.closedBall (0 : ℂ) 1)) :
    boundaryDSq (fun θ i => f (circlePoint θ) i) =
      ENNReal.ofReal ((2 * Real.pi)⁻¹) * normDiscArea f := by
  rw [normDiscArea_vector_eq_boundaryDSq hf, ← mul_assoc,
    ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (2 * Real.pi)⁻¹),
    inv_mul_cancel₀ (by positivity : 2 * Real.pi ≠ 0), ENNReal.ofReal_one, one_mul]

theorem euclideanArea_eq_boundaryDSq {q : ℕ} {f : ℂ → ComplexVector q}
    (hf : ContDiffOn ℂ ∞ f (Metric.closedBall (0 : ℂ) 1)) :
    euclideanArea f = ENNReal.ofReal (2 * Real.pi) * boundaryDSq (fun θ i => f (circlePoint θ) i) :=
  normDiscArea_vector_eq_boundaryDSq hf

theorem clockArea_eq_boundaryDSq {n : ℕ} {X : KahlerManifold n} {F : VariationDisc X}
    (hF : ContDiffOn ℂ ∞ F.w (Metric.closedBall (0 : ℂ) 1)) :
    clockArea F = ENNReal.ofReal (2 * Real.pi) * boundaryDSq (fun θ (_ : Unit) => F.w (circlePoint θ)) :=
  normDiscArea_scalar_eq_boundaryDSq hF

end Yau.Blueprint.V03Proof
