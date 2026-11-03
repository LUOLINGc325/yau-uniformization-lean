import Yau.Proofs.P04CanonicalOverlap

noncomputable section
open Set Filter MeasureTheory Bundle
open scoped Topology Manifold ContDiff

namespace Yau.Proofs.P04Aux
open Yau Yau.LeafProofs
variable {n : ℕ} {M : ComplexManifold n}

set_option backward.isDefEq.respectTransparency false in
/-- A top tensor is recovered by its single actual coefficient in any chart. -/
theorem topTensor_eq_of_chartCoefficient_eq (a x : M.Carrier)
    (hx : x ∈ (extChartAt (ComplexModel n) a).source)
    (u v : BundleDbar.NQForm (CanonicalCoefficients M) 0)
    (heq : BundleDbar.coefficients (r := 1) (CanonicalCoefficients M) u a (chartPt a x) Fin.elim0 0 =
      BundleDbar.coefficients (r := 1) (CanonicalCoefficients M) v a (chartPt a x) Fin.elim0 0) :
    u x=v x := by
  have hxs : x ∈ L14Aux.bundleChartSource (r := 1) (CanonicalCoefficients M) a := by
    rwa [coefficient_bundleChartSource]
  apply (L14Aux.topTensorCoordinatesEquiv (CanonicalCoefficients M) a x hxs).injective
  have hcoords (w : BundleDbar.NQForm (CanonicalCoefficients M) 0) :
      L14Aux.topTensorCoordinatesEquiv (CanonicalCoefficients M) a x hxs (w x) =
        BundleDbar.coefficients (CanonicalCoefficients M) w a (chartPt a x) Fin.elim0 := by
    rw [L14Aux.topTensorCoordinatesEquiv_apply,L14Aux.topTensorValueEquiv_form]
    ext α
    rw [L14Aux.coefficients_topFormValue]
    rw [show chartInv a (chartPt a x)=x from (extChartAt (ComplexModel n) a).left_inv hx]
  rw [hcoords,hcoords]
  ext α
  have hα : α=(0 : Fin 1) := Subsingleton.elim _ _
  subst α
  exact heq

/-- Intrinsic local AE representatives give AE equality of their actual
coefficients on overlaps, using the positive-volume chart map. -/
theorem top_coefficients_ae_on_overlap (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (a b : M.Carrier)
    (u v w : BundleDbar.NQForm (CanonicalCoefficients M) 0)
    (ha : ∀ᵐ x ∂μ.restrict ((extChartAt (ComplexModel n) a).source), u x=v x)
    (hb : ∀ᵐ x ∂μ.restrict ((extChartAt (ComplexModel n) b).source), u x=w x) :
    (fun z => BundleDbar.coefficients (r := 1) (CanonicalCoefficients M) v b z Fin.elim0 0)
      =ᵐ[(lebesgueC n).restrict (canonicalOverlap a b)]
    (fun z => BundleDbar.coefficients (r := 1) (CanonicalCoefficients M) w b z Fin.elim0 0) := by
  have hga := (ae_restrict_iff' (isOpen_extChartAt_source a).measurableSet).mp ha
  have hgb := (ae_restrict_iff' (isOpen_extChartAt_source b).measurableSet).mp hb
  have hglob : ∀ᵐ x ∂μ, x ∈ (extChartAt (ComplexModel n) a).source →
      x ∈ (extChartAt (ComplexModel n) b).source → v x=w x := by
    filter_upwards [hga,hgb] with x hA hB
    intro hxa hxb
    exact (hA hxa).symm.trans (hB hxb)
  have hlocal : ∀ᵐ x ∂μ.restrict (L14Aux.bundleChartSource (r := 1) (CanonicalCoefficients M) b),
      x ∈ (extChartAt (ComplexModel n) a).source →
      x ∈ (extChartAt (ComplexModel n) b).source → v x=w x := ae_restrict_of_ae hglob
  have hz := (L14Aux.chartInvExtension_quasiMeasurePreserving (CanonicalCoefficients M) g μ hμ b).ae hlocal
  rw [coefficient_localDomain] at hz
  have hzo := ae_restrict_of_ae_restrict_of_subset
    (show canonicalOverlap a b ⊆ chartTarget b from inter_subset_left) hz
  filter_upwards [hzo,ae_restrict_mem (canonicalOverlap_isOpen a b).measurableSet] with z hx hzs
  rw [Yau.LeafProofs.chartInvExtension,if_pos hzs.1] at hx
  have heq := hx hzs.2 ((extChartAt (ComplexModel n) b).map_target hzs.1)
  unfold BundleDbar.coefficients
  rw [heq]

end Yau.Proofs.P04Aux
