import Yau.Proofs.P04CanonicalGlue
import Yau.Proofs.P03WeakRegularity

noncomputable section
open Set Filter MeasureTheory Bundle
open scoped Topology Manifold ContDiff ENNReal

namespace Yau.Proofs.P04Aux
open Yau Yau.LeafProofs
variable {n : ℕ} {M : ComplexManifold n}

/-- Genuine homogeneous distributional dbar recovery, using the committed
scalar CR producer and the proved intrinsic canonical gluing construction. -/
theorem holomorphicTop_representative (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (u : BundleDbar.NQForm (CanonicalCoefficients M) 0)
    (hu : BundleDbar.WeakDbar (r := 1) (CanonicalCoefficients M) u
      (0 : BundleDbar.NQForm (CanonicalCoefficients M) 1)) :
    ∃ v : BundleDbar.NQForm (CanonicalCoefficients M) 0,
      BundleDbar.HolomorphicTopForm (r := 1) (CanonicalCoefficients M) v ∧ ∀ᵐ x ∂μ, u x=v x := by
  have hlocal (a : M.Carrier) : ∃ f : ComplexVector n → ℂ,
      DifferentiableOn ℂ f (chartTarget a) ∧
      (fun z => BundleDbar.coefficients (r := 1) (CanonicalCoefficients M) u a z Fin.elim0 0)
        =ᵐ[(lebesgueC n).restrict (chartTarget a)] f := by
    have H := Yau.NodeProofs.P03Aux.weakDbar_zero_holomorphic_coefficients
      (CanonicalCoefficients M) u hu a 0
    simpa only [coefficient_localDomain] using H
  choose f hf hae using hlocal
  exact glue_canonical_coefficients g μ hμ u f hf hae

/-- The recovered section carries the SAME finite weighted norm, measured
by the original actual canonical norm. -/
theorem canonical_holomorphic_weighted_representative (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (φ : M.Carrier → ℝ)
    (u : BundleDbar.NQForm (CanonicalCoefficients M) 0)
    (hu : BundleDbar.WeightedL2 (r := 1) (CanonicalCoefficients M) g.form flatMetric μ φ u)
    (hd : BundleDbar.WeakDbar (r := 1) (CanonicalCoefficients M) u
      (0 : BundleDbar.NQForm (CanonicalCoefficients M) 1)) :
    ∃ S : CanonicalSection M, IsHolomorphicCanonical S ∧
      (∀ᵐ x ∂μ, u x=canonicalToTop S x) ∧
      (∫⁻ x, ENNReal.ofReal (canonicalNormSq g.form S x*Real.exp (-φ x)) ∂μ) < ⊤ := by
  obtain ⟨v,hv,hae⟩ := holomorphicTop_representative g μ hμ u hd
  refine ⟨topToCanonical v,(holomorphicTop_iff v).mp hv,?_,?_⟩
  · simpa only [canonicalToTop_topToCanonical] using hae
  · have hW := L14Aux.weightedL2_of_ae_eq (CanonicalCoefficients M) g μ hμ flatMetric φ u v hu hae
    rw [← weightedNormSq_canonicalToTop g.form (topToCanonical v) μ φ,canonicalToTop_topToCanonical]
    exact hW.2

end Yau.Proofs.P04Aux
