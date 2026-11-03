import Yau.Proofs.V03HolomorphicScalarAreaVariation
import Yau.Proofs.V03HolomorphicVelocityTrace
import Yau.Proofs.V03CoordinateDerivative
import Yau.Proofs.V03VectorAreaFourier

/-! The actual Euclidean area of a joint holomorphic closed-disc family
has mixed derivative exactly 2π times the original velocity seminorm. -/

open scoped Topology ContDiff
open Filter

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

variable {q : ℕ} {U : Set ℂ} {H : ℂ × ℂ → ComplexVector q}

theorem euclideanFamilyArea_toReal_eq_sum
    (hH : ContDiffOn ℂ ∞ H (U ×ˢ Metric.closedBall (0 : ℂ) 1)) {z : ℂ} (hz : z ∈ U) :
    (euclideanArea (fun ζ => H (z, ζ))).toReal =
      ∑ b, (normDiscArea (fun ζ => H (z, ζ) b)).toReal := by
  have hs : ContDiffOn ℂ ∞ (fun ζ => H (z, ζ)) (Metric.closedBall (0 : ℂ) 1) :=
    hH.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun ζ hζ => ⟨hz, hζ⟩)
  change (normDiscArea (fun ζ => H (z, ζ))).toReal = _
  rw [normDiscArea_vector_eq_sum hs, ENNReal.toReal_sum
    (fun b _ => normDiscArea_ne_top_of_closedDisc ((contDiffOn_piLp 2).mp hs b))]

theorem euclideanFamilyArea_contDiffOn (hU : IsOpen U)
    (hH : ContDiffOn ℂ ∞ H (U ×ˢ Metric.closedBall (0 : ℂ) 1)) :
    ContDiffOn ℝ ∞ (fun z => (euclideanArea (fun ζ => H (z, ζ))).toReal) U := by
  have hHb (b : Fin q) : ContDiffOn ℂ ∞ (fun p => H p b) (U ×ˢ Metric.closedBall (0 : ℂ) 1) :=
    (contDiffOn_piLp 2).mp hH b
  have hEach (b : Fin q) : ContDiffOn ℝ ∞
      (fun z => (normDiscArea (fun ζ => H (z, ζ) b)).toReal) U :=
    holomorphicScalarArea_contDiffOn (H := fun p => H p b) hU (hHb b)
  have hs : ContDiffOn ℝ ∞ (fun z => ∑ b, (normDiscArea (fun ζ => H (z, ζ) b)).toReal) U :=
    ContDiffOn.sum (fun b _ => hEach b)
  exact hs.congr (fun z hz => euclideanFamilyArea_toReal_eq_sum hH hz)

theorem euclideanFamilyArea_mixed (hU : IsOpen U) (h0 : (0 : ℂ) ∈ U)
    (hH : ContDiffOn ℂ ∞ H (U ×ˢ Metric.closedBall (0 : ℂ) 1)) :
    mixedReal (fun z => (euclideanArea (fun ζ => H (z, ζ))).toReal) =
      (2 * Real.pi) * (boundaryDSq (fun θ b =>
        fderivWithin ℂ H (U ×ˢ Metric.closedBall (0 : ℂ) 1) (0, circlePoint θ) (1, 0) b)).toReal := by
  classical
  have hHb (b : Fin q) : ContDiffOn ℂ ∞ (fun p => H p b) (U ×ˢ Metric.closedBall (0 : ℂ) 1) :=
    (contDiffOn_piLp 2).mp hH b
  let f : Fin q → ℂ → ℝ := fun b z => (normDiscArea (fun ζ => H (z, ζ) b)).toReal
  have hf (b : Fin q) : ContDiffAt ℝ 2 (f b) 0 :=
    ((holomorphicScalarArea_contDiffOn (H := fun p => H p b) hU (hHb b)).contDiffAt
      (hU.mem_nhds h0)).of_le (by simp)
  have heq : (fun z => (euclideanArea (fun ζ => H (z, ζ))).toReal) =ᶠ[𝓝 (0 : ℂ)]
      (fun z => ∑ b, f b z) := by
    filter_upwards [hU.mem_nhds h0] with z hz
    exact euclideanFamilyArea_toReal_eq_sum hH hz
  have hS : UniqueDiffOn ℂ (U ×ˢ Metric.closedBall (0 : ℂ) 1) :=
    hU.uniqueDiffOn.prod uniqueDiffOn_complex_closedDisc
  have hcomponent (θ : ℝ) (b : Fin q) :
      jointParameterVelocity (fun p => H p b) U 0 1 (circlePoint θ) =
        fderivWithin ℂ H (U ×ˢ Metric.closedBall (0 : ℂ) 1) (0, circlePoint θ) (1, 0) b :=
    fderivWithin_euclidean_component (hS _ ⟨h0, circlePoint_mem_closedBall θ⟩)
      ((hH.differentiableOn (by simp)) _ ⟨h0, circlePoint_mem_closedBall θ⟩) (1, 0) b
  have hfin (b : Fin q) : boundaryDSq
      (fun θ (_ : Unit) => jointParameterVelocity (fun p => H p b) U 0 1 (circlePoint θ)) ≠ ⊤ :=
    jointParameterVelocity_boundaryDSq_ne_top (H := fun p => H p b) hU (hHb b) h0 1
  calc
    _ = mixedReal (fun z => ∑ b, f b z) := mixedReal_congr heq
    _ = ∑ b, mixedReal (f b) := mixedReal_finsetSum Finset.univ (fun b _ => hf b)
    _ = ∑ b, (2 * Real.pi) * (boundaryDSq
        (fun θ (_ : Unit) => jointParameterVelocity (fun p => H p b) U 0 1 (circlePoint θ))).toReal :=
      Finset.sum_congr rfl (fun b _ => holomorphicScalarArea_mixed (H := fun p => H p b) hU h0 (hHb b))
    _ = _ := by
      rw [← Finset.mul_sum]
      congr 1
      have hvec : (fun θ b => fderivWithin ℂ H (U ×ˢ Metric.closedBall (0 : ℂ) 1)
          (0, circlePoint θ) (1, 0) b) =
          (fun θ b => jointParameterVelocity (fun p => H p b) U 0 1 (circlePoint θ)) := by
        funext θ b
        exact (hcomponent θ b).symm
      rw [hvec, boundaryDSq_eq_sum_singleton
        (fun θ b => jointParameterVelocity (fun p => H p b) U 0 1 (circlePoint θ)),
        ENNReal.toReal_sum (fun b _ => hfin b)]

end Yau.Blueprint.V03Proof
