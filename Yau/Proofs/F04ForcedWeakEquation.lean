import Yau.Proofs.F04ForcedClassicalDivergence
import Yau.Proofs.F04ClassicalWeakEquation

open MeasureTheory Filter Set
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
namespace Yau.F04Proof
open Yau.Parabolic Yau.ParabolicCandidates Yau.LeafProofs.L16Aux

/-- A genuine smooth forced particular solution satisfies the exact weak
 equation with its actual source and its actual classical gradient. The
 source is separated only after all compact-test integrability is proved. -/
theorem forced_classical_weakEquation
    {n : ℕ} {O : Set (Space n)} (hO : IsOpen O) {S : ℝ}
    {a : Point n → Mat n} {b : Point n → RIdx n → ℝ} {u f : Point n → ℝ}
    (hSmooth : SmoothCoefficients (O ×ˢ Icc 0 S) a b)
    (hu : ContDiffOn ℝ ∞ u (O ×ˢ Ioo 0 S))
    (hf : ContDiffOn ℝ ∞ f (O ×ˢ Ioo 0 S))
    (hEq : ∀ p ∈ O ×ˢ Ioo 0 S, linearOp (O ×ˢ Icc 0 S) a b u p = f p) :
    WeakEquation O (Ioo 0 S) a b f u (dgGradient u) := by
  have hQ := hO.prod (isOpen_Ioo : IsOpen (Ioo (0 : ℝ) S))
  have hfields := homogeneous_classical_fields hO hSmooth hu
  have hclass := forced_classical_divergence hO hSmooth hu hEq
  let P := energyFlux a (dgGradient u)
  let R := fun p => ∑ j, energyDrift a b p j * dgGradient u p j
  have hPS (i : RIdx n) : ContDiffOn ℝ ∞ (fun p => P p i) (O ×ˢ Ioo 0 S) :=
    dgFlux_contDiffOn hQ hfields.1 hu i
  have hRS : ContDiffOn ℝ ∞ R (O ×ˢ Ioo 0 S) := by
    apply ContDiffOn.sum
    intro j _
    exact (hfields.2.1 j).mul (dgGradient_contDiffOn hQ hu j)
  have hweak := classical_weak_divergence hQ hu hPS (hRS.add hf)
    (fun p hp => by
      have hh := hclass p hp
      convert hh using 1
      rfl)
  intro φ hφ
  let L := fun p : Point n => deriv (fun t => φ (p.1, t)) p.2
  let J := fun p : Point n => ∑ i, P p i * d (fun x => φ (x, p.2)) p.1 i
  let E := fun p : Point n => -u p * L p + J p - R p * φ p
  have hUT : Integrable (u * L) (productVolume O (Ioo 0 S)) :=
    smooth_test_integrable hQ hu (test_timeDerivative hφ)
  have hJT : Integrable J (productVolume O (Ioo 0 S)) :=
    integrable_finsetSum Finset.univ (fun i _ =>
      smooth_test_integrable hQ (hPS i) (test_spatialDerivative hφ i))
  have hRT : Integrable (R * φ) (productVolume O (Ioo 0 S)) := smooth_test_integrable hQ hRS hφ
  have hFT : Integrable (fun p => f p * φ p) (productVolume O (Ioo 0 S)) :=
    smooth_test_integrable hQ hf hφ
  have hET : Integrable E (productVolume O (Ioo 0 S)) := by
    have he : E = (-(u * L) + J) - R * φ := by
      funext p
      change -u p * L p + J p - R p * φ p = -(u p * L p) + J p - R p * φ p
      ring
    rw [he]
    exact (hUT.neg.add hJT).sub hRT
  have hz := hweak φ hφ
  change (∫ p, -u p * L p + J p - (R p + f p) * φ p ∂productVolume O (Ioo 0 S)) = 0 at hz
  have he : (fun p => -u p * L p + J p - (R p + f p) * φ p) =
      (fun p => E p - f p * φ p) := by
    funext p
    dsimp only [E]
    ring
  rw [he, integral_sub hET hFT] at hz
  have hResult := sub_eq_zero.mp hz
  simpa only [E, J, P, R, L, energyFlux, energyDrift, Finset.sum_mul] using hResult

end Yau.F04Proof
