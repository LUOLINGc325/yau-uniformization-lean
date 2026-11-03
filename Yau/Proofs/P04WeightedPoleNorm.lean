import Yau.Proofs.P04PoleMultiplier
import Yau.Proofs.P04CanonicalRegularity

noncomputable section
open MeasureTheory Bundle
open scoped Topology Manifold ContDiff ENNReal

namespace Yau.Proofs.P04Aux
open Yau Yau.LeafProofs BundleDbar
variable {n : ℕ} {M : ComplexManifold n}

theorem canonical_formNormSq_multiply_real (g : HermitianField M)
    (χ : M.Carrier → ℝ) (u : NQForm (CanonicalCoefficients M) 0) (x : M.Carrier) :
    BundleDbar.formNormSq (r := 1) (CanonicalCoefficients M) g flatMetric
      (L14Aux.multiplyForm (CanonicalCoefficients M) (fun x => (χ x : ℂ)) u) x =
      χ x^2 * BundleDbar.formNormSq (r := 1) (CanonicalCoefficients M) g flatMetric u x := by
  have he : L14Aux.multiplyForm (CanonicalCoefficients M) (fun x => (χ x : ℂ)) u x =
      ((χ x : ℂ) • u) x := by
    apply Subtype.ext
    rfl
  rw [L14Aux.formNormSq_congr_at (CanonicalCoefficients M) g flatMetric _ _ x he,
    L14Aux.formNormSq_top_smul]
  simp only [Complex.normSq_ofReal,pow_two]

/-- Exact change of weight for the actual top tensor and measure. -/
theorem weightedNormSq_poleMultiplier (g : HermitianField M) (μ : Measure M.Carrier)
    (P Φ : M.Carrier → ℝ) (u : NQForm (CanonicalCoefficients M) 0) :
    weightedNormSq (r := 1) (CanonicalCoefficients M) g flatMetric μ Φ
      (L14Aux.multiplyForm (CanonicalCoefficients M) (fun x => (Real.exp (-P x/2) : ℂ)) u) =
      weightedNormSq (r := 1) (CanonicalCoefficients M) g flatMetric μ (fun x => Φ x+P x) u := by
  unfold weightedNormSq
  apply lintegral_congr
  intro x
  rw [canonical_formNormSq_multiply_real]
  congr 1
  calc
    _ = BundleDbar.formNormSq (r := 1) (CanonicalCoefficients M) g flatMetric u x *
        (Real.exp (-P x/2)^2*Real.exp (-Φ x)) := by ring
    _ = _ := by rw [poleMultiplier_weight_identity]

theorem weightedNormSq_antitone_weight (g : HermitianField M) (μ : Measure M.Carrier)
    {φ ψ : M.Carrier → ℝ} (h : ∀ x, φ x ≤ ψ x)
    (u : NQForm (CanonicalCoefficients M) 0) :
    weightedNormSq (r := 1) (CanonicalCoefficients M) g flatMetric μ ψ u ≤
      weightedNormSq (r := 1) (CanonicalCoefficients M) g flatMetric μ φ u := by
  apply lintegral_mono
  intro x
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg (h x)))
  exact L14Aux.formNormSq_top_nonneg (CanonicalCoefficients M) g flatMetric u x

theorem weightedL2_of_larger_weight (g : HermitianField M) (μ : Measure M.Carrier)
    {φ ψ : M.Carrier → ℝ} (h : ∀ x, φ x ≤ ψ x)
    (u : NQForm (CanonicalCoefficients M) 0)
    (hu : WeightedL2 (r := 1) (CanonicalCoefficients M) g flatMetric μ φ u) :
    WeightedL2 (r := 1) (CanonicalCoefficients M) g flatMetric μ ψ u :=
  ⟨hu.1,(weightedNormSq_antitone_weight g μ h u).trans_lt hu.2⟩

end Yau.Proofs.P04Aux
