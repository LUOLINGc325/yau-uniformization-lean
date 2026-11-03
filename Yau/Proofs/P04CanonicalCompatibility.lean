import Yau.Proofs.P04CanonicalOverlapAE

noncomputable section
open Set Filter MeasureTheory Bundle
open scoped Topology Manifold ContDiff

namespace Yau.Proofs.P04Aux
open Yau Yau.LeafProofs
variable {n : ℕ} {M : ComplexManifold n}

/-- Actual holomorphic local representatives agree pointwise on overlaps;
AE equalities are upgraded only on the open-positive coefficient domain. -/
theorem localCanonicalTop_compatible (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (a b : M.Carrier)
    (u : BundleDbar.NQForm (CanonicalCoefficients M) 0)
    (f k : ComplexVector n → ℂ)
    (hf : DifferentiableOn ℂ f (chartTarget a)) (hk : DifferentiableOn ℂ k (chartTarget b))
    (hfae : (fun z => BundleDbar.coefficients (r := 1) (CanonicalCoefficients M) u a z Fin.elim0 0)
      =ᵐ[(lebesgueC n).restrict (chartTarget a)] f)
    (hkae : (fun z => BundleDbar.coefficients (r := 1) (CanonicalCoefficients M) u b z Fin.elim0 0)
      =ᵐ[(lebesgueC n).restrict (chartTarget b)] k)
    {x : M.Carrier} (hxa : x ∈ (extChartAt (ComplexModel n) a).source)
    (hxb : x ∈ (extChartAt (ComplexModel n) b).source) :
    localCanonicalTop a f x=localCanonicalTop b k x := by
  have hA := localCanonicalTop_ae_on_chart g μ hμ a u f hfae
  have hB := localCanonicalTop_ae_on_chart g μ hμ b u k hkae
  have hae := top_coefficients_ae_on_overlap g μ hμ a b u
    (localCanonicalTop a f) (localCanonicalTop b k) hA hB
  have hcA := (localCanonicalTop_differentiableOn_overlap a b f hf).continuousOn
  have hcB : ContinuousOn
      (fun z => BundleDbar.coefficients (r := 1) (CanonicalCoefficients M)
        (localCanonicalTop b k) b z Fin.elim0 0) (canonicalOverlap a b) := by
    apply (hk.continuousOn.mono (show canonicalOverlap a b ⊆ chartTarget b from inter_subset_left)).congr
    intro z hz
    exact localCanonicalTop_coefficient b k hz.1
  letI : (lebesgueC n).IsOpenPosMeasure := by rw [lebesgueC_eq_volume]; infer_instance
  have heq := (lebesgueC n).eqOn_open_of_ae_eq hae (canonicalOverlap_isOpen a b) hcA hcB
  have hz : chartPt b x ∈ canonicalOverlap a b := by
    refine ⟨(extChartAt (ComplexModel n) b).map_source hxb,?_⟩
    change chartInv b (chartPt b x) ∈ (extChartAt (ComplexModel n) a).source
    rw [show chartInv b (chartPt b x)=x from (extChartAt (ComplexModel n) b).left_inv hxb]
    exact hxa
  exact topTensor_eq_of_chartCoefficient_eq b x hxb _ _ (heq hz)

end Yau.Proofs.P04Aux
