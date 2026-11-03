import Yau.Proofs.C01CompactUniformMetricComparison
import Yau.Proofs.C01CompactNormCoercivity

/-! Tangent norm comparison controls the actual extended path length
on each confined segment, without an integrability assumption on a
restricted segment. -/

noncomputable section

open MeasureTheory Filter
open scoped Topology Manifold ContDiff ENNReal

namespace Yau.NodeProofs.C01Aux

open Yau Yau.Blueprint
open Yau.LeafProofs.L12Aux Yau.LeafProofs.L23Aux

variable {n : ℕ} {M : ComplexManifold n}

def actualPathSpeed (k : HermitianField M) (f : ℝ → M.Carrier) (s : ℝ) : ℝ :=
  Real.sqrt (2 * hermitianNormSq (k (f s)) (realTangentEquiv (f s) (realCurveVelocity f s)))

def actualPathELength (k : HermitianField M) (f : ℝ → M.Carrier) (a b : ℝ) : ℝ≥0∞ := by
  letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentNormedAddCommGroup k z
  exact Manifold.pathELength 𝓘(ℝ, ComplexVector n) f a b

theorem actualPathELength_eq_lintegral (k : HermitianField M) (f : ℝ → M.Carrier) (a b : ℝ) :
    actualPathELength k f a b = ∫⁻ s in Set.Icc a b, ENNReal.ofReal (actualPathSpeed k f s) := by
  letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentNormedAddCommGroup k z
  rw [actualPathELength, Manifold.pathELength_eq_lintegral_mfderiv_Icc]
  apply lintegral_congr
  intro s
  rw [← ofReal_norm]
  change ENNReal.ofReal ‖realCurveVelocity f s‖ = _
  rw [underlyingRealTangent_norm]
  rfl

theorem actualPathELength_lower_of_speedSq_lower
    (k₀ k₁ : HermitianField M) (K : Set M.Carrier) (ell : ℝ) (hell : 0 ≤ ell)
    (hmetric : ∀ x ∈ K, ∀ v : TangentVector M x,
      ell ^ 2 * (2 * hermitianNormSq (k₀ x) v) ≤ 2 * hermitianNormSq (k₁ x) v)
    (f : ℝ → M.Carrier) {a b : ℝ} (himage : Set.MapsTo f (Set.Icc a b) K) :
    ENNReal.ofReal ell * actualPathELength k₀ f a b ≤ actualPathELength k₁ f a b := by
  rw [actualPathELength_eq_lintegral, actualPathELength_eq_lintegral,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
  have H := Real.sqrt_le_sqrt (hmetric (f s) (himage hs)
    (realTangentEquiv (f s) (realCurveVelocity f s)))
  rw [Real.sqrt_mul (sq_nonneg ell), Real.sqrt_sq hell] at H
  rw [← ENNReal.ofReal_mul hell]
  exact ENNReal.ofReal_le_ofReal H

theorem actualPathELength_upper_of_speedSq_upper
    (k₀ k₁ : HermitianField M) (K : Set M.Carrier) (ell : ℝ) (hell : 0 ≤ ell)
    (hmetric : ∀ x ∈ K, ∀ v : TangentVector M x,
      2 * hermitianNormSq (k₁ x) v ≤ ell ^ 2 * (2 * hermitianNormSq (k₀ x) v))
    (f : ℝ → M.Carrier) {a b : ℝ} (himage : Set.MapsTo f (Set.Icc a b) K) :
    actualPathELength k₁ f a b ≤ ENNReal.ofReal ell * actualPathELength k₀ f a b := by
  rw [actualPathELength_eq_lintegral, actualPathELength_eq_lintegral,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
  have H := Real.sqrt_le_sqrt (hmetric (f s) (himage hs)
    (realTangentEquiv (f s) (realCurveVelocity f s)))
  rw [Real.sqrt_mul (sq_nonneg ell), Real.sqrt_sq hell] at H
  rw [← ENNReal.ofReal_mul hell]
  exact ENNReal.ofReal_le_ofReal H

end Yau.NodeProofs.C01Aux
